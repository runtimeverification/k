in skool-untyped-syntax
in skool-untyped-semantics
in skool-untyped-programs



----------------------------
--- SKOOL-UNTYPED module ---
----------------------------

kmod SKOOL-UNTYPED is including SKOOL-UNTYPED-SEMANTICS + SKOOL-UNTYPED-PROGRAMS 
--- make sure the name of the final module is the capitalized version of the file name

---<OO stuff added>
--- internal form of a program

--- kpgm label is used to traverse a program and to build the content of the <pgm>..</pgm> cell
  syntax KLabel ::= kpgm

--- global variables (for now they should be declared at the beginning of the program)

  rule <k> kpgm(var X:Id;  Ss) => kpgm(Ss) <_/k>
       <class> object </class>
       <env> Env:Map => Env[L / X] </env> 
       <store_> .Map => L |-> 0 <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 

  rule <k> kpgm(var X:Id;) => . <_/k>
       <class> object </class>
       <env> Env:Map => Env[L / X] </env> 
       <store_> .Map => L |-> 0 <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 

--- a class traversal
  rule <k> kpgm(class C1:Id extends C2:Id { Ss:Stmts }) => kpgm(Ss) <_/k>
       <class> C:Id => C1 </class>
       <pgm_> . => <classes_>
                           <className> C1 </className>          
                           <extends> C2 </extends>
                   <_/classes>
       <_/pgm>

--- variable declaration
  rule <k> kpgm(var X:Id;  Ss) => kpgm(Ss) <_/k>
       <class> C </class>
       <pgm_>
             <classes_>
                     <className> C </className>
                     <fields_> . => var X; </fields>
             <_/classes>
       </pgm>
  rule <k> kpgm(var X:Id;) => . <_/k>   --- the var declaration is the last
       <class> C </class>
       <pgm_>
             <classes_>
                     <className> C </className>
                     <fields_> . => var X; </fields>
             <_/classes>
       </pgm>

  rule <k> kpgm(var X[ N:Nat ] ;  Ss) => kpgm(Ss) <_/k>
       <class> C </class>
       <pgm_>
             <classes_>
                     <className> C </className>
                     <fields_> . => var X[N]; </fields>
             <_/classes>
       </pgm>
  rule <k> kpgm(var X[ N:Nat ];) => . <_/k>   --- the array declaration is the last
       <class> C </class>
       <pgm_>
             <classes_>
                     <className> C </className>
                     <fields_> . => var X[N]; </fields>
             <_/classes>
       </pgm>

--- a method traversal
  rule <k> kpgm(method F:Id(Xl:List{Id}) S:Stmt  Ss) => kpgm(Ss) <_/k>
       <class> C </class>
       <pgm_>
             <classes_>
                     <className> C </className>
                     <methods_> . => method F(Xl) S </methods>
             <_/classes>
       </pgm> 
       <env> Env:Map => Env[L/[C, F]] </env>  
       <nextLoc> L:Nat => L +Nat 2 </nextLoc> 
       <store_>(.Map => L |-> function(sNat L) sNat(L) |-> lambda(Xl,S))<_/store>
  rule <k> kpgm(method F:Id(Xl) S:Stmt) => . <_/k>    --- the method declaration is the last
       <class> C </class>
       <pgm_>
             <classes_>
                     <className> C </className>
                     <methods_> . => method F(Xl) S </methods>
             <_/classes>
       </pgm> 
       <env> Env:Map => Env[L/[C, F]] </env>  
       <nextLoc> L:Nat => L +Nat 2 </nextLoc> 
       <store_>(.Map => L |-> function(sNat L) sNat(L) |-> lambda(Xl,S))<_/store>

--- sequence of statements
  
  rule <k> kpgm(Ss1:Stmts Ss2:Stmts) => kpgm(Ss1)~>kpgm(Ss2) <_/k>

---</OO stuff added>

  syntax Bag ::= run ( KLabel )

--- After loading simple-untyped-compiled into maude, type "rew run .".
---     Replace pSorting by any other program, then recompile
  macro run(K:KLabel)
        =
        <T_> 
           <k> kpgm(K(.List{K})) </k>
           <in> 
              List(7,,23,,654,,656,,54,,456,,436345647643567,,
                   354654364356,,4357643576)
           </in>
        <_/T> 

endkm



