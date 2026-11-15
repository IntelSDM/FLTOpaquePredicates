#include "FLTOpaquePass.h"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <random>
#include <string>
#include <vector>

using namespace llvm;

llvm::cl::opt<bool> FLTOpaqueEnable("obfflt", llvm::cl::init(true), llvm::cl::desc("Fermat's Little Theorem modular exp path explosion opaque."));

static constexpr unsigned PrimeCount = 128;
static constexpr uint64_t PrimeMin = 1ull << 19;
static constexpr uint64_t PrimeMax = 1ull << 21;
static constexpr unsigned VerifySamples = 2000;

// i32 pool primes in [2^12, 2^14] so 2*BitLen is in [24,28]; Barrett magic fits in u32 and product of two factors fits in u32, which breaks for any larger prime width at this type
static constexpr unsigned PrimeCount32 = 32;
static constexpr uint64_t PrimeMin32 = 1ull << 12;
static constexpr uint64_t PrimeMax32 = 1ull << 14;
static_assert(PrimeMax32 <= (1ull << 16), "i32 prime square must fit in u32");

static constexpr unsigned Width32Pct = 25;

static constexpr unsigned PerFunctionCap = 16;
static constexpr unsigned MinBBInsts = 2;
static constexpr bool SkipEntry = false;
static constexpr bool SkipLoops = false;

static constexpr unsigned BarrierPoolSize = 24;

static constexpr unsigned PolluteMinOps = 8;
static constexpr unsigned PolluteMaxOps = 48;
static constexpr unsigned DiamondCap = 16;
static constexpr unsigned StealCeiling = 16;
static constexpr unsigned StealMinRealBB = 5;

static_assert(PrimeMax <= (1ull << 32), "PrimeMax squaring would overflow i64");

// intra ladder reductions pick between urem and Barrett per site; the initial xPrep→base0 reduction MUST always use urem because xPrep is an arbitrary u64, not constrained to P², so Barrett's "v < 2^(2*BitLen)" precondition does not hold and Barrett there returns garbage that routes compare to pollute
static constexpr unsigned FormUrem = 70;
static constexpr unsigned FormBarrett = 30;
static_assert(FormUrem + FormBarrett == 100, "form weights must sum to 100");

enum class ReductionForm { Urem, Barrett };

static constexpr unsigned WeightA = 40;
static constexpr unsigned WeightB = 30;
static constexpr unsigned WeightC = 15;
static constexpr unsigned WeightD = 15;
static_assert(WeightA + WeightB + WeightC + WeightD == 100, "variant weights must sum to 100");

struct FLTPrime
{
    uint64_t P;
    unsigned BitLen;
    uint64_t BarrettMagic;
    unsigned BarrettShift;
};

static std::vector<FLTPrime> FltPrimes;
static std::vector<FLTPrime> FltPrimes32;

static uint64_t MulMod(uint64_t a, uint64_t b, uint64_t m)
{
    return (a * b) % m;
}

static uint64_t PowMod(uint64_t base, uint64_t exp, uint64_t m)
{
    uint64_t r = 1 % m;
    base %= m;
    while (exp > 0)
    {
        if (exp & 1) r = MulMod(r, base, m);
        exp >>= 1;
        if (exp) base = MulMod(base, base, m);
    }
    return r;
}

static bool MillerRabin(uint64_t n, uint64_t a)
{
    if (n % a == 0) return n == a;
    uint64_t d = n - 1;
    unsigned r = 0;
    while ((d & 1) == 0) { d >>= 1; ++r; }
    uint64_t x = PowMod(a, d, n);
    if (x == 1 || x == n - 1) return true;
    for (unsigned i = 0; i < r - 1; ++i)
    {
        x = MulMod(x, x, n);
        if (x == n - 1) return true;
    }
    return false;
}

static bool IsPrime(uint64_t n)
{
    if (n < 2) return false;
    if (n < 4) return true;
    if ((n & 1) == 0) return false;
    for (uint64_t a : { 2ull, 3ull, 5ull, 7ull, 11ull, 13ull, 17ull })
    {
        if (a >= n) break;
        if (!MillerRabin(n, a)) return false;
    }
    return true;
}

static unsigned BitLengthOf(uint64_t v)
{
    unsigned n = 0;
    while (v) { ++n; v >>= 1; }
    return n;
}

// sampled FLT verifier covers 2000 random bases per prime, which rejects pseudoprime stragglers Miller Rabin's 7 witness suite missed on a particular draw; dropping this check lets a none prime P slip into the pool, and then pow(x,P) mod P != x mod P for the first attacker chosen x and the site routes to pollute on legitimate input
static bool VerifyFLT(uint64_t P, std::mt19937_64& rng)
{
    for (unsigned i = 0; i < VerifySamples; ++i)
    {
        uint64_t x = rng();
        if (PowMod(x, P, P) != x % P) return false;
    }
    return true;
}

static void BuildPoolInto(std::vector<FLTPrime>& pool, uint64_t pmin, uint64_t pmax, unsigned target, uint64_t seed)
{
    pool.clear();
    std::mt19937_64 rng(seed);

    std::vector<uint64_t> candidates;
    candidates.reserve(target * 4);

    const unsigned span = (unsigned)(pmax - pmin);
    unsigned attempts = 0;
    const unsigned attemptcap = target * 128;
    while (candidates.size() < target * 2u && attempts < attemptcap)
    {
        ++attempts;
        uint64_t cand = pmin + (uint64_t)(rng() % span);
        cand |= 1;
        if (!IsPrime(cand)) continue;
        candidates.push_back(cand);
    }

    for (uint64_t p : candidates)
    {
        if (pool.size() >= target) break;
        if (!VerifyFLT(p, rng)) continue;
        if (p == 0) continue;

        FLTPrime fp;
        fp.P = p;
        fp.BitLen = BitLengthOf(p);
        fp.BarrettShift = 2u * fp.BitLen;
        fp.BarrettMagic = (uint64_t(1) << fp.BarrettShift) / p;
        pool.push_back(fp);
    }
}

static void BuildFLTPrimePool(uint64_t seed64, uint64_t seed32)
{
    BuildPoolInto(FltPrimes, PrimeMin, PrimeMax, PrimeCount, seed64);
    BuildPoolInto(FltPrimes32, PrimeMin32, PrimeMax32, PrimeCount32, seed32);
}

struct FLTBarrierState
{
    Module* M = nullptr;
    std::vector<GlobalVariable*> Slots;
    std::vector<uint64_t> SlotKeys;
    unsigned RoundRobin = 0;
    std::mt19937_64 Rng;
};

static FLTBarrierState Barrier;

// slot sharing across sites is safe because each caller's XOR constant is `K_S ^ target`; the slot's runtime value is K_S so XOR yields that caller's target, but a reader attacker can't recover K_S from one site because the XOR constant hides it, and a volatile load blocks LLVM constant propagation across sites sharing a slot
static void FLTBarrierInit(Module& m, uint64_t seed)
{
    Barrier.M = &m;
    Barrier.Slots.clear();
    Barrier.SlotKeys.clear();
    Barrier.RoundRobin = 0;
    Barrier.Rng.seed(seed);

    LLVMContext& ctx = m.getContext();
    IntegerType* i64 = Type::getInt64Ty(ctx);

    for (unsigned i = 0; i < BarrierPoolSize; ++i)
    {
        const std::string name = ".FltopqBarrier." + std::to_string(i);
        auto* gv = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), name);
        gv->setUnnamedAddr(GlobalValue::UnnamedAddr::None);
        gv->setAlignment(Align(8));
        Barrier.Slots.push_back(gv);

        uint64_t k = Barrier.Rng();
        if (k == 0) k = 0xDEADBEEFCAFEBABEULL;
        k |= 1ull;
        Barrier.SlotKeys.push_back(k);
    }
}

static Value* FLTInsertFoldBarrier(IRBuilder<>& b, uint64_t targetvalue)
{
    LLVMContext& ctx = b.getContext();
    IntegerType* i64 = Type::getInt64Ty(ctx);

    const unsigned slotidx = Barrier.RoundRobin % (unsigned)Barrier.Slots.size();
    Barrier.RoundRobin++;
    GlobalVariable* slot = Barrier.Slots[slotidx];
    const uint64_t ks = Barrier.SlotKeys[slotidx];

    LoadInst* ld = b.CreateLoad(i64, slot, true, "FltBarLd");
    ld->setAlignment(Align(8));
    return b.CreateXor(ld, ConstantInt::get(i64, ks ^ targetvalue), "FltBarUnk");
}

static Value* FLTInsertFoldBarrierT(IRBuilder<>& b, uint64_t targetvalue, IntegerType* ity)
{
    if (ity->getBitWidth() == 64) return FLTInsertFoldBarrier(b, targetvalue);
    Value* v64 = FLTInsertFoldBarrier(b, targetvalue);
    return b.CreateTrunc(v64, ity, "FltBarTr");
}

// priority 101 is the floor for user ctors on MSVC; the init writer MUST run before any protected function's site side volatile load, so another ctor at priority 103+ depending on the barrier slots works (the barrier init wrote them), but a ctor at priority <=100 would read zeros and the first-caller XOR would yield `K_S ^ target` which is NOT target
static void FLTBarrierFinalize()
{
    if (!Barrier.M) return;
    if (Barrier.Slots.empty()) return;
    if (Barrier.RoundRobin == 0) return;

    Module& m = *Barrier.M;
    LLVMContext& ctx = m.getContext();
    IntegerType* i64 = Type::getInt64Ty(ctx);

    FunctionType* ft = FunctionType::get(Type::getVoidTy(ctx), false);
    Function* initfn = Function::Create(ft, GlobalValue::InternalLinkage, "FltopqBarrierInit", &m);
    initfn->addFnAttr(Attribute::NoInline);
    BasicBlock* entry = BasicBlock::Create(ctx, "Entry", initfn);
    IRBuilder<> ib(entry);
    for (unsigned i = 0; i < Barrier.Slots.size(); ++i)
    {
        StoreInst* st = ib.CreateStore(ConstantInt::get(i64, Barrier.SlotKeys[i]), Barrier.Slots[i]);
        st->setVolatile(true);
        st->setAlignment(Align(8));
    }
    ib.CreateRetVoid();
    appendToGlobalCtors(m, initfn, 101);
}

static GlobalVariable* SaltGV = nullptr;

static void EnsureFLTSalt(Module& m)
{
    if (SaltGV) return;
    LLVMContext& ctx = m.getContext();
    IntegerType* i64 = Type::getInt64Ty(ctx);

    SaltGV = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), ".FltopqRdtscSalt");
    SaltGV->setUnnamedAddr(GlobalValue::UnnamedAddr::None);
    SaltGV->setAlignment(Align(8));

    FunctionType* ft = FunctionType::get(Type::getVoidTy(ctx), false);
    Function* saltinit = Function::Create(ft, GlobalValue::InternalLinkage, "FltopqSaltInit", &m);
    saltinit->addFnAttr(Attribute::NoInline);
    BasicBlock* entry = BasicBlock::Create(ctx, "Entry", saltinit);
    IRBuilder<> ib(entry);
    Function* rdtsc = Intrinsic::getDeclaration(&m, Intrinsic::readcyclecounter);
    Value* tsc = ib.CreateCall(rdtsc, {}, "FltRdtsc");
    StoreInst* st = ib.CreateStore(tsc, SaltGV);
    st->setVolatile(true);
    st->setAlignment(Align(8));
    ib.CreateRetVoid();

    appendToGlobalCtors(m, saltinit, 102);
}

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "obfus"); }
static bool HasNoObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "noobfus"); }
static bool HasNoFLTAnnotation(Function& f) { return HasAnnotationTag(f, "nofltopq"); }

static std::mt19937_64 Rng;

static constexpr const char* DoneMD = "fltopq.done";
static constexpr const char* PolluteMD = "fltopq.pollute";

static bool BBAlreadyProcessed(BasicBlock* bb)
{
    Instruction* t = bb->getTerminator();
    if (!t) return true;
    return t->getMetadata(DoneMD) != nullptr;
}

static void MarkBBProcessed(BasicBlock* bb)
{
    Instruction* t = bb->getTerminator();
    if (!t) return;
    t->setMetadata(DoneMD, MDNode::get(bb->getContext(), {}));
}

static bool IsPolluteBlock(BasicBlock* bb)
{
    Instruction* t = bb->getTerminator();
    if (!t) return false;
    return t->getMetadata(PolluteMD) != nullptr;
}

static void MarkPolluteBlock(BasicBlock* bb)
{
    Instruction* t = bb->getTerminator();
    if (!t) return;
    t->setMetadata(PolluteMD, MDNode::get(bb->getContext(), {}));
}

static bool IsEHOrFuncletInterior(BasicBlock* bb)
{
    if (bb->isEHPad()) return true;
    Instruction* t = bb->getTerminator();
    if (!t) return true;
    if (isa<CatchReturnInst>(t) || isa<CleanupReturnInst>(t) || isa<ResumeInst>(t)) return true;
    for (Instruction& i : *bb)
    {
        if (auto* cb = dyn_cast<CallBase>(&i))
        {
            if (cb->countOperandBundlesOfType(LLVMContext::OB_funclet) > 0) return true;
        }
    }
    return false;
}

static Instruction* PickInsertionPoint(BasicBlock* bb)
{
    Instruction* first = bb->getFirstNonPHIOrDbgOrLifetime();
    if (!first) return nullptr;
    if ((unsigned)bb->size() < MinBBInsts) return nullptr;

    // entry block split before an alloca would demote that alloca from static to dynamic, breaking AllocaInst::isStaticAlloca downstream — clamp `first` past the last entry alloca
    if (bb == &bb->getParent()->getEntryBlock())
    {
        Instruction* lastalloca = nullptr;
        for (Instruction& i : *bb)
        {
            if (isa<AllocaInst>(&i)) lastalloca = &i;
        }
        if (lastalloca)
        {
            Instruction* after = lastalloca->getNextNode();
            if (!after) return nullptr;
            BasicBlock::iterator seek(first);
            while (seek != bb->end() && &*seek != after) ++seek;
            if (seek != bb->end()) first = &*seek;
            else first = after;
        }
    }

    unsigned splittable = 0;
    for (auto it = BasicBlock::iterator(first); it != bb->end(); ++it)
    {
        if (&*it == bb->getTerminator()) break;
        ++splittable;
    }
    if (splittable == 0) return nullptr;

    const unsigned pick = (unsigned)(Rng() % splittable);
    BasicBlock::iterator it(first);
    for (unsigned i = 0; i < pick; ++i) ++it;
    if (it == bb->end()) return nullptr;
    if (&*it == bb->getTerminator()) return nullptr;
    if (isa<PHINode>(&*it)) return nullptr;
    return &*it;
}

static std::vector<Value*> HarvestAux(IRBuilder<>& b, DominatorTree& dt, Instruction* insertbefore, unsigned want, std::mt19937_64& rng)
{
    LLVMContext& ctx = b.getContext();
    IntegerType* i64 = Type::getInt64Ty(ctx);
    Function* f = insertbefore->getFunction();
    BasicBlock* ipbb = insertbefore->getParent();

    std::vector<Value*> candidates;

    for (Argument& a : f->args())
    {
        if (a.getType()->isIntegerTy(64)) candidates.push_back(&a);
        else if (a.getType()->isIntegerTy(32)) candidates.push_back(b.CreateZExt(&a, i64, "FltAuxZx"));
    }

    for (BasicBlock& bb : *f)
    {
        if (&bb == ipbb)
        {
            for (Instruction& i : bb)
            {
                if (&i == insertbefore) break;
                if (i.getType()->isIntegerTy(64)) candidates.push_back(&i);
                else if (i.getType()->isIntegerTy(32)) candidates.push_back(&i);
            }
            continue;
        }
        if (!dt.dominates(&bb, ipbb)) continue;
        for (Instruction& i : bb)
        {
            if (i.getType()->isIntegerTy(64)) candidates.push_back(&i);
            else if (i.getType()->isIntegerTy(32)) candidates.push_back(&i);
        }
    }

    std::vector<Value*> picked;
    if (candidates.empty())
    {
        for (unsigned i = 0; i < want; ++i) picked.push_back(FLTInsertFoldBarrier(b, (uint64_t)rng()));
        return picked;
    }

    SmallPtrSet<Value*, 8> seen;
    unsigned tries = 0;
    while (picked.size() < want && tries < want * 8)
    {
        ++tries;
        Value* v = candidates[(size_t)(rng() % candidates.size())];
        if (!seen.insert(v).second) continue;
        if (v->getType()->isIntegerTy(32)) v = b.CreateZExt(v, i64, "FltAuxZx");
        picked.push_back(v);
    }
    while (picked.size() < want) picked.push_back(FLTInsertFoldBarrier(b, (uint64_t)rng()));
    return picked;
}

// Barrett `v * magic` can reach ~2^(3*BitLen), which overflows `ity` for small widths (i32 Barrett overflows at BitLen > ~10); widen mul+shift to i64 unconditionally and trunc the quotient back to ity before the conditional subtract (which stays in ity)
static Value* EmitReduce(IRBuilder<>& b, Value* v, const FLTPrime& prime, ReductionForm form)
{
    IntegerType* ity = cast<IntegerType>(v->getType());
    Value* pb = FLTInsertFoldBarrierT(b, prime.P, ity);
    if (form == ReductionForm::Urem)
    {
        return b.CreateURem(v, pb, "FltRu");
    }
    IntegerType* i64 = Type::getInt64Ty(b.getContext());
    Value* vw = (ity->getBitWidth() == 64) ? v : b.CreateZExt(v, i64, "FltRBvw");
    Value* magicw = FLTInsertFoldBarrier(b, prime.BarrettMagic);
    Value* prodw = b.CreateMul(vw, magicw, "FltRBm");
    Value* qw = b.CreateLShr(prodw, ConstantInt::get(i64, prime.BarrettShift), "FltRBq");
    Value* q = (ity->getBitWidth() == 64) ? qw : b.CreateTrunc(qw, ity, "FltRBqt");
    Value* qp = b.CreateMul(q, pb, "FltRBqp");
    Value* t = b.CreateSub(v, qp, "FltRBt");
    Value* needssub = b.CreateICmpUGE(t, pb, "FltRBc");
    Value* corrected = b.CreateSub(t, pb, "FltRBts");
    return b.CreateSelect(needssub, corrected, t, "FltRBr");
}

static ReductionForm PickReductionForm(std::mt19937_64& rng)
{
    return ((unsigned)(rng() % 100u) < FormUrem) ? ReductionForm::Urem : ReductionForm::Barrett;
}

static Value* EmitStraightLineFLT(IRBuilder<>& b, Value* xprep, const FLTPrime& prime, ReductionForm form)
{
    IntegerType* ity = cast<IntegerType>(xprep->getType());
    Value* base = EmitReduce(b, xprep, prime, ReductionForm::Urem);
    Value* acc = FLTInsertFoldBarrierT(b, 1ull, ity);

    const uint64_t p = prime.P;
    const unsigned bl = prime.BitLen;
    for (unsigned bitidx = 0; bitidx < bl; ++bitidx)
    {
        const bool setbit = ((p >> bitidx) & 1ull) != 0;
        if (setbit)
        {
            // acc < P and base < P so prod < P² < 2^(2*BitLen), which satisfies Barrett's precondition; any ladder step that violates acc<P invariantly would feed Barrett a too large value and the final compare flips to pollute
            Value* prod = b.CreateMul(acc, base, "FltAccxbase");
            acc = EmitReduce(b, prod, prime, form);
        }
        if (bitidx + 1 < bl)
        {
            Value* sq = b.CreateMul(base, base, "FltBasesq");
            base = EmitReduce(b, sq, prime, form);
        }
    }
    return acc;
}

struct LoopEmitResult
{
    Value* FinalAcc;
    BasicBlock* AfterLoop;
};

// loop MD requires the outer MDNode's first operand to reference the node itself (replaceOperandWith(0, loopmd)); without the self reference LLVM's loop pass manager asserts on malformed loop MD and the unroll disable hint is lost, which lets LoopUnrollPass unroll the ladder and defeats the path explosion
static LoopEmitResult EmitLoopFLT(Function& f, BasicBlock* headbb, Value* xprep, const FLTPrime& prime, ReductionForm form)
{
    LLVMContext& ctx = f.getContext();
    IntegerType* ity = cast<IntegerType>(xprep->getType());

    IRBuilder<> headb(headbb);
    Value* base0 = EmitReduce(headb, xprep, prime, ReductionForm::Urem);
    Value* acc0 = FLTInsertFoldBarrierT(headb, 1ull, ity);
    Value* exp0 = FLTInsertFoldBarrierT(headb, prime.P, ity);
    Value* iter0 = ConstantInt::get(ity, 0);
    Value* trip = FLTInsertFoldBarrierT(headb, (uint64_t)prime.BitLen, ity);

    BasicBlock* loopheader = BasicBlock::Create(ctx, "LoopHdr", &f);
    BasicBlock* loopbody = BasicBlock::Create(ctx, "LoopBody", &f);
    BasicBlock* afterloop = BasicBlock::Create(ctx, "AfterLoop", &f);

    headb.CreateBr(loopheader);

    IRBuilder<> lhb(loopheader);
    PHINode* accphi = lhb.CreatePHI(ity, 2, "FltLAcc");
    PHINode* basephi = lhb.CreatePHI(ity, 2, "FltLBase");
    PHINode* expphi = lhb.CreatePHI(ity, 2, "FltLExp");
    PHINode* iterphi = lhb.CreatePHI(ity, 2, "FltLIter");
    accphi->addIncoming(acc0, headbb);
    basephi->addIncoming(base0, headbb);
    expphi->addIncoming(exp0, headbb);
    iterphi->addIncoming(iter0, headbb);
    lhb.CreateBr(loopbody);

    IRBuilder<> lbb(loopbody);
    Value* bit = lbb.CreateAnd(expphi, ConstantInt::get(ity, 1), "FltLBit");
    Value* cond = lbb.CreateICmpEQ(bit, ConstantInt::get(ity, 1), "FltLBc");
    Value* prod = lbb.CreateMul(accphi, basephi, "FltLAxb");
    Value* accm = EmitReduce(lbb, prod, prime, form);
    Value* accsel = lbb.CreateSelect(cond, accm, accphi, "FltLAss");

    Value* sq = lbb.CreateMul(basephi, basephi, "FltLSq");
    Value* basenext = EmitReduce(lbb, sq, prime, form);

    Value* expnext = lbb.CreateLShr(expphi, ConstantInt::get(ity, 1), "FltLEn");
    Value* iternext = lbb.CreateAdd(iterphi, ConstantInt::get(ity, 1), "FltLIn");
    Value* done = lbb.CreateICmpUGE(iternext, trip, "FltLDone");

    MDBuilder mdb(ctx);
    MDNode* weights = mdb.createBranchWeights(1u, 100000u);
    BranchInst* lbbr = lbb.CreateCondBr(done, afterloop, loopheader);
    lbbr->setMetadata(LLVMContext::MD_prof, weights);

    MDNode* unrolldisable = MDNode::get(ctx, { MDString::get(ctx, "llvm.loop.unroll.disable") });
    MDNode* loopmd = MDNode::get(ctx, { nullptr, unrolldisable });
    loopmd->replaceOperandWith(0, loopmd);
    lbbr->setMetadata(LLVMContext::MD_loop, loopmd);

    accphi->addIncoming(accsel, loopbody);
    basephi->addIncoming(basenext, loopbody);
    expphi->addIncoming(expnext, loopbody);
    iterphi->addIncoming(iternext, loopbody);

    IRBuilder<> alb(afterloop);
    PHINode* finalaccphi = alb.CreatePHI(ity, 1, "FltLFinal");
    finalaccphi->addIncoming(accsel, loopbody);

    return { finalaccphi, afterloop };
}

static Value* EmitCompareRecipe(IRBuilder<>& b, Value* lhs, Value* rhs, std::mt19937_64& rng, bool& outrealontrue)
{
    IntegerType* ity = cast<IntegerType>(lhs->getType());
    const uint64_t nonce = rng();
    Value* noncev = FLTInsertFoldBarrierT(b, nonce, ity);
    Value* lhsn = b.CreateXor(lhs, noncev, "FltCmpLhsn");
    Value* noncev2 = FLTInsertFoldBarrierT(b, nonce, ity);
    Value* rhsn = b.CreateXor(rhs, noncev2, "FltCmpRhsn");

    switch (rng() % 4u)
    {
        case 0:
            outrealontrue = true;
            return b.CreateICmpEQ(lhsn, rhsn, "FltCmpEq");
        case 1:
            outrealontrue = false;
            return b.CreateICmpNE(lhsn, rhsn, "FltCmpNe");
        case 2:
        {
            Value* diff = b.CreateSub(lhsn, rhsn, "FltCmpSub");
            Value* zero = FLTInsertFoldBarrierT(b, 0ull, ity);
            outrealontrue = true;
            return b.CreateICmpEQ(diff, zero, "FltCmpEqz");
        }
        case 3:
        default:
        {
            Value* diff = b.CreateXor(lhsn, rhsn, "FltCmpXor");
            Value* zero = FLTInsertFoldBarrierT(b, 0ull, ity);
            outrealontrue = true;
            return b.CreateICmpEQ(diff, zero, "FltCmpEqxz");
        }
    }
}

struct PolluteSlot
{
    AllocaInst* Base;
    int FieldIdx;
    Type* BaseTy;
    Type* RawTy;
    bool IsPtr;
    IntegerType* IntTy;
};

static Value* MaterializeSlotPtr(IRBuilder<>& b, const PolluteSlot& s)
{
    if (s.FieldIdx < 0) return s.Base;
    LLVMContext& ctx = b.getContext();
    IntegerType* i32 = Type::getInt32Ty(ctx);
    return b.CreateInBoundsGEP(s.BaseTy, s.Base, { ConstantInt::get(i32, 0), ConstantInt::get(i32, s.FieldIdx) }, "FltPGep");
}

static Value* EmitSlotLoad(IRBuilder<>& b, const PolluteSlot& s)
{
    Value* ptr = MaterializeSlotPtr(b, s);
    LoadInst* ld = b.CreateLoad(s.RawTy, ptr, "FltPl");
    if (!s.IsPtr) return ld;
    return b.CreatePtrToInt(ld, s.IntTy, "FltPli");
}

static void EmitSlotStore(IRBuilder<>& b, const PolluteSlot& s, Value* intval, bool vol)
{
    Value* ptr = MaterializeSlotPtr(b, s);
    Value* v = intval;
    if (s.IsPtr) v = b.CreateIntToPtr(intval, s.RawTy, "FltPip");
    StoreInst* st = b.CreateStore(v, ptr);
    if (vol) st->setVolatile(true);
}

static void CollectPolluteSlots(Function& f, IntegerType* i32, IntegerType* i64, SmallVectorImpl<PolluteSlot>& out32, SmallVectorImpl<PolluteSlot>& out64)
{
    for (Instruction& i : f.getEntryBlock())
    {
        auto* a = dyn_cast<AllocaInst>(&i);
        if (!a || !a->isStaticAlloca()) continue;
        Type* ty = a->getAllocatedType();

        if (ty->isIntegerTy(32)) { out32.push_back({ a, -1, ty, ty, false, i32 }); continue; }
        if (ty->isIntegerTy(64)) { out64.push_back({ a, -1, ty, ty, false, i64 }); continue; }
        if (ty->isPointerTy()) { out64.push_back({ a, -1, ty, ty, true, i64 }); continue; }

        if (auto* st = dyn_cast<StructType>(ty))
        {
            for (unsigned fi = 0; fi < st->getNumElements(); ++fi)
            {
                Type* ft = st->getElementType(fi);
                if (ft->isIntegerTy(32)) out32.push_back({ a, (int)fi, ty, ft, false, i32 });
                else if (ft->isIntegerTy(64)) out64.push_back({ a, (int)fi, ty, ft, false, i64 });
                else if (ft->isPointerTy()) out64.push_back({ a, (int)fi, ty, ft, true, i64 });
            }
        }
    }
}

static GlobalVariable* GetOrCreateFLTSink(Module& m, unsigned idx)
{
    const std::string name = ".FltopqSink." + std::to_string(idx % 8);
    if (auto* existing = m.getGlobalVariable(name)) return existing;
    LLVMContext& ctx = m.getContext();
    IntegerType* i64 = Type::getInt64Ty(ctx);
    auto* gv = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), name);
    gv->setUnnamedAddr(GlobalValue::UnnamedAddr::None);
    gv->setAlignment(Align(8));
    return gv;
}

// shift/div operand 1 MUST be left unperturbed because perturbation would produce an out of range shift amount or a divide by zero, which LLVM's verifier rejects (shift) or lowers to poison (div); constant perturbation on binop operand 0 and none shift binops is safe
static unsigned DiamondCloneRealIntoPollute(BasicBlock* realbb, BasicBlock* pollutebb, std::mt19937_64& rng, unsigned maxclone)
{
    if (maxclone == 0) return 0;

    ValueToValueMapTy vmap;
    unsigned cloned = 0;
    const uint64_t mutnonce = rng();

    for (Instruction& i : *realbb)
    {
        if (cloned >= maxclone) break;
        if (i.isTerminator()) break;

        if (isa<PHINode>(&i)) continue;
        if (isa<AllocaInst>(&i)) continue;
        if (isa<CallBase>(&i)) continue;
        if (isa<LandingPadInst>(&i)) continue;
        if (isa<CatchPadInst>(&i)) continue;
        if (isa<CleanupPadInst>(&i)) continue;
        if (i.isAtomic()) continue;
        if (isa<FenceInst>(&i)) continue;

        bool allok = true;
        for (Use& u : i.operands())
        {
            Value* op = u.get();
            auto* oi = dyn_cast<Instruction>(op);
            if (!oi) continue;
            if (vmap.count(op)) continue;
            if (oi->getParent() != realbb && oi->getParent() != pollutebb) continue;
            allok = false;
            break;
        }
        if (!allok) continue;

        Instruction* clone = i.clone();
        clone->setName("");
        clone->insertInto(pollutebb, pollutebb->end());
        RemapInstruction(clone, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);

        if (auto* bo = dyn_cast<BinaryOperator>(clone))
        {
            const Instruction::BinaryOps opc = bo->getOpcode();
            const bool divorshift = (opc == Instruction::UDiv || opc == Instruction::SDiv || opc == Instruction::URem || opc == Instruction::SRem || opc == Instruction::Shl || opc == Instruction::LShr || opc == Instruction::AShr);
            if (!divorshift && (rng() & 1u) == 0)
            {
                Instruction::BinaryOps newop = opc;
                switch (opc)
                {
                    case Instruction::Add: newop = Instruction::Sub; break;
                    case Instruction::Sub: newop = Instruction::Add; break;
                    case Instruction::And: newop = Instruction::Or; break;
                    case Instruction::Or: newop = Instruction::And; break;
                    case Instruction::Xor: newop = Instruction::Or; break;
                    case Instruction::Mul: newop = Instruction::Add; break;
                    default: break;
                }
                if (newop != opc)
                {
                    IRBuilder<> bb(bo);
                    Value* nb = bb.CreateBinOp(newop, bo->getOperand(0), bo->getOperand(1));
                    bo->replaceAllUsesWith(nb);
                    vmap[&i] = nb;
                    bo->eraseFromParent();
                    ++cloned;
                    continue;
                }
            }
            for (unsigned op = 0; op < bo->getNumOperands(); ++op)
            {
                if (divorshift && op == 1) continue;
                if (auto* ci = dyn_cast<ConstantInt>(bo->getOperand(op)))
                {
                    if ((rng() % 100u) < 50u)
                    {
                        bo->setOperand(op, ConstantInt::get(ci->getType(), ci->getZExtValue() ^ mutnonce));
                    }
                }
            }
        }
        else if (auto* si = dyn_cast<StoreInst>(clone))
        {
            if ((rng() % 100u) < 30u)
            {
                Value* v = si->getValueOperand();
                if (auto* iv = dyn_cast<IntegerType>(v->getType()))
                {
                    IRBuilder<> bb(si);
                    Value* nv = bb.CreateXor(v, ConstantInt::get(iv, mutnonce), "");
                    si->setOperand(0, nv);
                }
            }
        }

        vmap[&i] = clone;
        ++cloned;
    }

    return cloned;
}

static void FillPolluteBlock(Function& f, BasicBlock* pollutebb, BasicBlock* realbb, BasicBlock* headbb, std::mt19937_64& rng)
{
    LLVMContext& ctx = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(ctx);
    IntegerType* i64 = Type::getInt64Ty(ctx);

    SmallVector<PolluteSlot, 32> slots32, slots64;
    CollectPolluteSlots(f, i32, i64, slots32, slots64);

    SmallVector<Value*, 16> vals32, vals64;
    for (Argument& a : f.args())
    {
        if (a.getType()->isIntegerTy(32)) vals32.push_back(&a);
        else if (a.getType()->isIntegerTy(64)) vals64.push_back(&a);
    }
    for (Instruction& i : *headbb)
    {
        if (i.getType()->isIntegerTy(32)) vals32.push_back(&i);
        else if (i.getType()->isIntegerTy(64)) vals64.push_back(&i);
    }

    const bool have32 = !slots32.empty();
    const bool have64 = !slots64.empty();

    const unsigned diamondcap = std::min<unsigned>((unsigned)(realbb->size() > 1 ? realbb->size() - 1 : 0), DiamondCap);
    const unsigned diamondcloned = DiamondCloneRealIntoPollute(realbb, pollutebb, rng, diamondcap);

    IRBuilder<> pollb(pollutebb);

    if (!have32 && !have64)
    {
        GlobalVariable* sink = GetOrCreateFLTSink(*f.getParent(), (unsigned)rng());
        LoadInst* ld = pollb.CreateLoad(i64, sink, true, "FltSinkLd");
        ld->setAlignment(Align(8));
        Value* mixed = pollb.CreateXor(ld, ConstantInt::get(i64, rng()), "FltSinkMx");
        StoreInst* st = pollb.CreateStore(mixed, sink);
        st->setVolatile(true);
        st->setAlignment(Align(8));
        pollb.CreateBr(realbb);
        return;
    }

    pollb.SetInsertPoint(pollutebb);

    unsigned targetops = (unsigned)realbb->size();
    if (targetops < PolluteMinOps) targetops = PolluteMinOps;
    if (targetops > PolluteMaxOps) targetops = PolluteMaxOps;
    if (diamondcloned >= targetops) targetops = 2;
    else targetops -= diamondcloned;

    Value* acc = nullptr;
    IntegerType* accty = nullptr;

    auto pickslot = [&](IntegerType* ity) -> const PolluteSlot&
    {
        auto& slots = (ity == i64) ? slots64 : slots32;
        return slots[rng() % slots.size()];
    };

    for (unsigned n = 0; n < targetops; ++n)
    {
        IntegerType* ity;
        if (have32 && have64) ity = (rng() & 1) ? i64 : i32;
        else ity = have64 ? i64 : i32;

        if (acc && accty != ity) acc = nullptr;

        if (!acc || (rng() % 5) == 0)
        {
            acc = EmitSlotLoad(pollb, pickslot(ity));
            accty = ity;
            continue;
        }

        auto& vals = (ity == i64) ? vals64 : vals32;
        Value* rhs = nullptr;
        const unsigned pick = (unsigned)(rng() % 10u);
        if (pick < 6) rhs = EmitSlotLoad(pollb, pickslot(ity));
        else if (pick < 9 && !vals.empty()) rhs = vals[rng() % vals.size()];
        else rhs = ConstantInt::get(ity, rng());

        switch (rng() % 7)
        {
            case 0: acc = pollb.CreateAdd(acc, rhs, "FltPa"); break;
            case 1: acc = pollb.CreateSub(acc, rhs, "FltPs"); break;
            case 2: acc = pollb.CreateXor(acc, rhs, "FltPx"); break;
            case 3: acc = pollb.CreateAnd(acc, rhs, "FltPn"); break;
            case 4: acc = pollb.CreateOr(acc, rhs, "FltPo"); break;
            case 5: acc = pollb.CreateMul(acc, rhs, "FltPm"); break;
            default:
            {
                const unsigned w = ity->getBitWidth();
                unsigned shamt = (unsigned)(rng() % (w - 1u)) + 1u;
                acc = pollb.CreateShl(acc, ConstantInt::get(ity, shamt), "FltPsh");
                break;
            }
        }

        if ((rng() % 100) < 15) EmitSlotStore(pollb, pickslot(ity), acc, false);
    }

    if (acc) EmitSlotStore(pollb, pickslot(accty), acc, true);

    pollb.CreateBr(realbb);
}

static unsigned StealIntoHead(BasicBlock* headbb, BasicBlock* realbb, unsigned maxsteal)
{
    unsigned stolen = 0;
    while (stolen < maxsteal)
    {
        Instruction* first = realbb->getFirstNonPHIOrDbgOrLifetime();
        if (!first || first->isTerminator()) break;

        if (isa<CallBase>(first)) break;
        if (isa<AllocaInst>(first)) break;
        if (isa<LandingPadInst>(first)) break;
        if (isa<CatchPadInst>(first)) break;
        if (isa<CleanupPadInst>(first)) break;
        if (first->isAtomic()) break;
        if (isa<FenceInst>(first)) break;
        if (first->mayHaveSideEffects()) break;

        bool opsok = true;
        for (Use& op : first->operands())
        {
            Value* v = op.get();
            if (auto* oi = dyn_cast<Instruction>(v))
            {
                if (oi->getParent() == realbb) { opsok = false; break; }
            }
        }
        if (!opsok) break;

        first->removeFromParent();
        first->insertInto(headbb, headbb->end());
        ++stolen;
    }
    return stolen;
}

// rdtsc salt at priority 102 keeps xPrep unreducible by LLVM constant propagation even when the aux harvest found no runtime values; a site that wouldn't otherwise depend on anything runtime still gets a per process start random offset, and the ctor priority MUST sit above the barrier init (101) so the salt slot is valid by the time any site runs
static Value* BuildXPrep(IRBuilder<>& builder, DominatorTree& dt, Function& f, Instruction* anchor, IntegerType* ity, std::mt19937_64& rng)
{
    LLVMContext& ctx = f.getContext();
    IntegerType* i64 = Type::getInt64Ty(ctx);

    const unsigned auxcount = 2u + (unsigned)(rng() % 2u);
    std::vector<Value*> aux = HarvestAux(builder, dt, anchor, auxcount, rng);

    Value* xmix = aux[0];
    for (size_t ai = 1; ai < aux.size(); ++ai) xmix = builder.CreateXor(xmix, aux[ai], "FltXmix");

    EnsureFLTSalt(*f.getParent());
    LoadInst* saltld = builder.CreateLoad(i64, SaltGV, true, "FltSalt");
    saltld->setAlignment(Align(8));
    Value* xsalted = builder.CreateXor(xmix, saltld, "FltXsalt");

    Value* zeroopaque = FLTInsertFoldBarrier(builder, 0ull);
    Value* x64 = builder.CreateXor(xsalted, zeroopaque, "FltXprep64");
    if (ity->getBitWidth() == 64) return x64;
    return builder.CreateTrunc(x64, ity, "FltXprep");
}

struct VariantEmitResult
{
    Value* Cond;
    bool RealOnTrue;
    BasicBlock* ContinueBB;
    bool Ok;
    unsigned LadderOpCount;
};

static VariantEmitResult EmitVariantA(Function& f, BasicBlock* headbb, DominatorTree& dt, const FLTPrime& prime, ReductionForm form, IntegerType* ity, std::mt19937_64& rng)
{
    IRBuilder<> builder(headbb);
    Value* anchor = FLTInsertFoldBarrier(builder, (uint64_t)rng());
    Instruction* anchori = cast<Instruction>(anchor);

    Value* xprep = BuildXPrep(builder, dt, f, anchori, ity, rng);
    Value* ladderresult = EmitStraightLineFLT(builder, xprep, prime, form);
    Value* rhs = EmitReduce(builder, xprep, prime, ReductionForm::Urem);

    bool realontrue = true;
    Value* cond = EmitCompareRecipe(builder, ladderresult, rhs, rng, realontrue);

    return { cond, realontrue, headbb, true, prime.BitLen };
}

static VariantEmitResult EmitVariantB(Function& f, BasicBlock* headbb, DominatorTree& dt, const FLTPrime& prime, ReductionForm form, IntegerType* ity, std::mt19937_64& rng)
{
    IRBuilder<> builder(headbb);
    Value* anchor = FLTInsertFoldBarrier(builder, (uint64_t)rng());
    Instruction* anchori = cast<Instruction>(anchor);

    Value* xprep = BuildXPrep(builder, dt, f, anchori, ity, rng);

    LoopEmitResult lr = EmitLoopFLT(f, headbb, xprep, prime, form);
    if (!lr.FinalAcc || !lr.AfterLoop) return { nullptr, true, nullptr, false, 0 };

    IRBuilder<> alb(lr.AfterLoop);
    Value* rhs = EmitReduce(alb, xprep, prime, ReductionForm::Urem);

    bool realontrue = true;
    Value* cond = EmitCompareRecipe(alb, lr.FinalAcc, rhs, rng, realontrue);

    return { cond, realontrue, lr.AfterLoop, true, prime.BitLen };
}

// variant C's chained double REQUIRES p1.P < p2.P so r1 < P1 < P2 and `r1 mod P2 == r1`; without the ordering r1 can be >= P2, the outer reduction aliases r1 to r1-P2, and the final compare `r2 == x mod P1` fails on legitimate input and routes to pollute
static VariantEmitResult EmitVariantC(Function& f, BasicBlock* headbb, DominatorTree& dt, const FLTPrime& p1, const FLTPrime& p2, ReductionForm form, IntegerType* ity, std::mt19937_64& rng)
{
    IRBuilder<> builder(headbb);
    Value* anchor = FLTInsertFoldBarrier(builder, (uint64_t)rng());
    Instruction* anchori = cast<Instruction>(anchor);

    Value* xprep = BuildXPrep(builder, dt, f, anchori, ity, rng);

    Value* r1 = EmitStraightLineFLT(builder, xprep, p1, form);
    Value* r2 = EmitStraightLineFLT(builder, r1, p2, form);

    Value* rhs = EmitReduce(builder, xprep, p1, ReductionForm::Urem);

    bool realontrue = true;
    Value* cond = EmitCompareRecipe(builder, r2, rhs, rng, realontrue);

    return { cond, realontrue, headbb, true, p1.BitLen + p2.BitLen };
}

static VariantEmitResult EmitVariantD(Function& f, BasicBlock* headbb, DominatorTree& dt, const FLTPrime& p1, const FLTPrime& p2, ReductionForm form, IntegerType* ity, std::mt19937_64& rng)
{
    IRBuilder<> builder(headbb);
    Value* anchor = FLTInsertFoldBarrier(builder, (uint64_t)rng());
    Instruction* anchori = cast<Instruction>(anchor);

    Value* xprep = BuildXPrep(builder, dt, f, anchori, ity, rng);

    Value* h1 = EmitStraightLineFLT(builder, xprep, p1, form);
    Value* h2 = EmitStraightLineFLT(builder, xprep, p2, form);
    Value* lhs = builder.CreateAdd(h1, h2, "FltDSum");

    Value* r1 = EmitReduce(builder, xprep, p1, ReductionForm::Urem);
    Value* r2 = EmitReduce(builder, xprep, p2, ReductionForm::Urem);
    Value* rhs = builder.CreateAdd(r1, r2, "FltDK");

    bool realontrue = true;
    Value* cond = EmitCompareRecipe(builder, lhs, rhs, rng, realontrue);

    return { cond, realontrue, headbb, true, p1.BitLen + p2.BitLen };
}

static bool TryEmitAtBB(Function& f, BasicBlock* bb, DominatorTree& dt, BasicBlock*& outrealbb)
{
    if (BBAlreadyProcessed(bb)) return false;
    if (SkipEntry && bb == &f.getEntryBlock()) return false;
    if (IsEHOrFuncletInterior(bb)) return false;
    if (bb->size() < MinBBInsts) return false;

    Instruction* splitat = PickInsertionPoint(bb);
    if (!splitat) return false;

    if (FltPrimes.empty()) return false;

    const unsigned vroll = (unsigned)(Rng() % 100u);
    enum class Variant { A, B, C, D } chosen;
    unsigned cum = 0;
    cum += WeightA;
    if (vroll < cum) chosen = Variant::A;
    else { cum += WeightB; if (vroll < cum) chosen = Variant::B;
    else { cum += WeightC; if (vroll < cum) chosen = Variant::C;
    else chosen = Variant::D; } }

    LLVMContext& ctx = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(ctx);
    IntegerType* i64 = Type::getInt64Ty(ctx);
    // i32 chosen only when the i32 pool is none empty; a width pick that falls back to an empty pool would panic in `pool[Rng() % pool.size()]`; the fallback forces i64 and MUST update both `use32` and `ity` before the second pool selection or the variant runs with the wrong type
    bool use32 = (!FltPrimes32.empty()) && ((unsigned)(Rng() % 100u) < Width32Pct);
    IntegerType* ity = use32 ? i32 : i64;

    std::vector<FLTPrime>& activepool = use32 ? FltPrimes32 : FltPrimes;
    if (activepool.empty())
    {
        use32 = false;
        ity = i64;
    }
    std::vector<FLTPrime>& pool = use32 ? FltPrimes32 : FltPrimes;

    const FLTPrime* p1 = &pool[Rng() % pool.size()];
    const FLTPrime* p2 = nullptr;

    // pick two from the SAME pool so C/D operate at one width; mixing an i64 prime with an i32 prime would feed a 20-bit value into an i32 Barrett magic computed for a 14-bit prime, and the reduction wraps modulo 2^32 instead of modulo P
    auto picktwofrompool = [&](bool ordered) -> bool
    {
        if (pool.size() < 2) return false;
        const size_t i1 = Rng() % pool.size();
        size_t i2 = Rng() % pool.size();
        unsigned tries = 0;
        while (i2 == i1 && tries < 8) { i2 = Rng() % pool.size(); ++tries; }
        if (i2 == i1) return false;
        const FLTPrime* a = &pool[i1];
        const FLTPrime* b = &pool[i2];
        if (ordered)
        {
            if (a->P > b->P) std::swap(a, b);
            if (a->P == b->P) return false;
        }
        p1 = a;
        p2 = b;
        return true;
    };

    if (chosen == Variant::C)
    {
        if (!picktwofrompool(true)) chosen = Variant::A;
    }
    else if (chosen == Variant::D)
    {
        if (!picktwofrompool(false)) chosen = Variant::A;
    }

    BasicBlock* realbb = bb->splitBasicBlock(splitat, "Cont");
    BasicBlock* pollutebb = BasicBlock::Create(ctx, "Cont", &f, realbb);

    Instruction* splitbr = bb->getTerminator();
    splitbr->eraseFromParent();

    const ReductionForm form = PickReductionForm(Rng);

    VariantEmitResult vr;
    switch (chosen)
    {
        case Variant::A: vr = EmitVariantA(f, bb, dt, *p1, form, ity, Rng); break;
        case Variant::B: vr = EmitVariantB(f, bb, dt, *p1, form, ity, Rng); break;
        case Variant::C: vr = EmitVariantC(f, bb, dt, *p1, *p2, form, ity, Rng); break;
        case Variant::D: vr = EmitVariantD(f, bb, dt, *p1, *p2, form, ity, Rng); break;
    }

    if (!vr.Ok)
    {
        vr = EmitVariantA(f, bb, dt, *p1, form, ity, Rng);
        chosen = Variant::A;
    }

    FillPolluteBlock(f, pollutebb, realbb, bb, Rng);
    MarkPolluteBlock(pollutebb);

    unsigned stealcap = 0;
    const unsigned rbsize = (unsigned)realbb->size();
    if (rbsize > StealMinRealBB)
    {
        const unsigned headroom = rbsize - StealMinRealBB;
        const unsigned ceiling = std::min<unsigned>(StealCeiling, headroom);
        stealcap = 1u + (unsigned)(Rng() % ceiling);
        const unsigned floor = std::min<unsigned>(4u, ceiling);
        if (stealcap < floor) stealcap = floor;
    }
    if (stealcap > 0) (void)StealIntoHead(vr.ContinueBB, realbb, stealcap);

    IRBuilder<> builder(vr.ContinueBB);
    if (vr.RealOnTrue) builder.CreateCondBr(vr.Cond, realbb, pollutebb);
    else builder.CreateCondBr(vr.Cond, pollutebb, realbb);

    MarkBBProcessed(bb);
    if (vr.ContinueBB != bb) MarkBBProcessed(vr.ContinueBB);

    outrealbb = realbb;
    return true;
}

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (HasNoObfuscateAnnotation(f) || HasNoFLTAnnotation(f)) return false;
    if (!HasObfuscateAnnotation(f)) return false;

    SmallVector<BasicBlock*, 64> worklist;
    SmallPtrSet<BasicBlock*, 32> seen;
    for (BasicBlock& bb : f)
    {
        worklist.push_back(&bb);
        seen.insert(&bb);
    }

    unsigned emitted = 0;
    bool mutated = false;

    while (!worklist.empty() && emitted < PerFunctionCap)
    {
        BasicBlock* bb = worklist.pop_back_val();
        if (IsPolluteBlock(bb)) continue;

        DominatorTree dt;
        dt.recalculate(f);
        LoopInfo li;
        li.analyze(dt);
        if (SkipLoops && li.getLoopFor(bb) != nullptr) continue;

        BasicBlock* realbb = nullptr;
        if (!TryEmitAtBB(f, bb, dt, realbb)) continue;

        ++emitted;
        mutated = true;

        if (realbb && seen.insert(realbb).second) worklist.push_back(realbb);
    }

    return mutated;
}

bool RunFLTOpaque(Module& m)
{
    if (!FLTOpaqueEnable) return false;

    std::random_device rd;
    uint64_t seed = (uint64_t)rd();
    seed ^= (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count();
    seed ^= ((uint64_t)rd()) << 32;
    seed ^= 0x464C544F50515F5FULL;
    Rng.seed(seed);

    // every module scoped pointer MUST be reset per invocation; a stale pointer carried over from a previous module would reach into reclaimed storage when the lazy create check skips, and THIS module needs its own fresh salt / barrier / prime pools
    SaltGV = nullptr;

    BuildFLTPrimePool(Rng(), Rng());
    if (FltPrimes.empty()) return false;

    FLTBarrierInit(m, Rng());

    bool mutated = false;
    for (Function& f : m) mutated |= ProcessFunction(f);

    FLTBarrierFinalize();

    FltPrimes.clear();
    FltPrimes32.clear();
    return mutated;
}

PreservedAnalyses FLTOpaquePass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunFLTOpaque(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}