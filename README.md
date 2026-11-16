# Fermat's Little Theorem Opaque Predicates
Built for LLVM 19.1 - Windows x64 <br> <br>

So the basic idea is a^p ≡ a (mod p), So to solve a condition you are at O(p), this forces timing out before you can actually resolve the condition. <br>
Its quite a simple equation of immense overhead to symbolically resolve the condition, given enough time it is resolvable but not realistically achievable. <br> 
This large scale overhead makes  it perfect for above head security in places like Nessa binaries. <br>
This paper: [Advancing Code Obfuscation: Novel Opaque Predicate Techniques to Counter Dynamic Symbolic Execution](https://www.sciopen.com/local/article_pdf/10.32604/cmc.2025.062743.pdf) has proven to time out KLEE and cause full false negatives with angr. <br>

<img width="1377" height="902" alt="image" src="https://github.com/user-attachments/assets/f0a9d8cc-db8b-4af0-b842-16fc42ec009a" /><br> 
<img width="1999" height="942" alt="image" src="https://github.com/user-attachments/assets/039a23db-feeb-441c-955a-43ffdd30664a" /><br> 
<img width="1978" height="963" alt="image" src="https://github.com/user-attachments/assets/49cc6983-e657-4d03-a424-7fe7249dea69" /><br> 
<img width="1405" height="313" alt="image" src="https://github.com/user-attachments/assets/3feadd22-d0ed-439e-8601-05393e7497f3" /><br> 
<img width="1852" height="850" alt="image" src="https://github.com/user-attachments/assets/3dfe6ba3-b392-45a1-a92e-cdd30f0ed799" /><br> 
