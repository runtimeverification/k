// 30 semantic rules
// 16 syntax translation macros
kmod KERNELC-SEMANTICS is 
  including KERNELC-DESUGARED-SYNTAX + K + PL-CONVERSION + PL-RANDOM

  /*@ 
     \section{KERNELC semantics}

       This module describes the basic configuration and semantics for the KERNELC language.  The semantics contains 30 semantic rules and 16 translation macros.

     \subsection{Configuration}
      
     The basic configuration for KERNELC contains a computation cell {\sf k}, an environment cell mapping (local) variables to values, a function stack cell for  saving the control context upon calling a function, input and output cells, a memory cell mapping location (represented as naturals) to values (integers), a ptr cell for maintaining information about memory blocks allocation sizes,  a counter for generating fresh locations and integers, and a {\sf rand} cell to help in the random number generation process.
  */
  configuration 
  <T multiplicity="?"> 
      <k color="green"> .K </k> 
      <env color="yellow"> .Map </env> 
      <funs color="ForestGreen"> .Map </funs>               @latex("\\kBR")
      <fstack color="LawnGreen"> .List </fstack>
      <in color="magenta"> .List </in> 
      <out color="Fuchsia"> "" </out> 
      <mem color="orange"> .Map </mem> 
      <ptr color="OrangeRed"> .Map </ptr> 
      <next> 0 </next> 
      <rand> 0 </rand>
  </T> 
  <result multiplicity="?"> "" </result>

  /*@ \subsection{Operations on local variables}
      Local variables in KERNELC are restricted.  They cannot be shared, cannot be addressed, and therefore reside in a separate space called the environment.

      Since their behavior does not depand on the interaction of threads, accesses to them are considered structural when analyzing thread interactions.
  */
  rule <k> X:Id => V <_/k>       <env_> X |-> V <_/env>    [structural]
  rule <k> X:Id ++ => I <_/k>    <env_> X |-> (I => I +Int 1) <_/env> 
  [structural]
  rule <k> X = V => V <_/k>      <env_> X |-> (_ => V) <_/env> [structural]


 //@ \subsection{Arithmentic expressions}
  rule I1 + I2 => I1 +Int I2 [structural]
  rule I1 - I2 => _-Int_(I1,I2) [structural]
  rule I1 % I2 => I1 %Int I2 if I2 !=Int 0 [structural]
  rule I1 <= I2 => Bool2Int(I1 <=Int I2) [structural]
  rule I1 < I2 => Bool2Int(I1 <Int I2) [structural]
  rule I1:Int == I2:Int => Bool2Int(I1 ==Int I2) [structural] 
  rule I1 != I2 =>  Bool2Int((I1 !=Int I2)) [structural]
  rule '_?_:_ => 'if`(_`)_else_  [structural]

  //@ \subsection{Conditional and loop}
  rule if(I)_ else St:Stmt => St if I ==Int 0 [structural]
  rule if(I:Int) St else _ => St if notBool(I ==Int 0) [structural]
  rule <k> while(E:Exp) St => if (E) {St while(E) St} else {} <_/k> 
  [structural]


  /*@ \subsection{Input/Output}
     These are proper rules as order interaction with the input/output channels is important for thread interaction.

     We chose here to desugar {\tt scanf} into an assignment to allow potential interleavings between the action of reading from the input buffer and that of writing into memory. 
  */
  rule [print]: <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>
  rule [read-global]: <k> scanf("%d",N:Nat) => (*N) = I <_/k> <in> (ListItem(I) => .) <_/in>
  rule [read-local]: <k> scanf("%d",&X) => X = I <_/k> <in> (ListItem(I) => .) <_/in>

  //@ \subsection{basic statements}
  rule V:Val ; => . [structural]
  rule {Sts:StmtList} => Sts  [structural]
  rule {} => .  [structural]
  rule St Sts => St ~> Sts [structural]


  //@ \subsection{Function declaration and function call}
  rule <k> __`{_`}(int X, Xl:List{DeclId}, Sts) => . <_/k> 
       <funs_> . => X |-> int X(Xl) { Sts } <_/funs> 
  [structural]
  rule __`{_`}((void_(X) => int_(X)), Xl:List{DeclId}, (Sts => __(Sts, return void;))) 
  [structural]

  syntax ListItem ::=  Id # Map # K 

  rule <k> '_`(_`)(X,,Vl:List{Val}) ~> K => Sts </k> 
    <env> Env => (eraseKLabel('int_,getList{K}(Xl)) |-> getList{K}(Vl)) </env>
    @latex("\\kBR")    <funs_> X |->  int X(Xl) { Sts } <_/funs> 
    <fstack> . => X # Env:Map # K:K <_/fstack>
  [structural large]

  context int _ = [HOLE]
  rule <k> int X => void <_/k> 
       <env_> . => (X |-> undef) <_/env> 
  [structural]
 
  rule <k> return V ; ~> _ => V </k> [structural]

  rule <k> V ~> (. => K) </k> <env> _ => Env </env> 
       <fstack> _ # Env # K => . <_/fstack> [structural]

  rule <k> random() => randomRandom(N') <_/k>
       <rand> N':Nat => N' +Nat 1 </rand>

  rule <k> srandom(I) => void <_/k>

  context *[HOLE]=_
  context (*[HOLE])++
  
  syntax Val ::= Int | void 
  syntax Exp ::= Val 
  syntax K ::= List{Exp} | List{PointerId} | List{DeclId} | StmtList | Pgm | String | undef | restore ( Map ) 
  syntax KResult ::= List{Val} 


  //@ \subsection{Auxiliary functions}
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N,,N1..N [structural]

  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto] 
  syntax List{Exp} ::= List{Val} 
endkm

kmod KERNELC-SIMPLE-MALLOC is including KERNELC-SEMANTICS
  /*@ \section{A simple memory allocator} 

      The rules below define a very simple memory allocation mechanism, which basically allocates memory in order, starting with the location following the last allocated location.  Since the memory is not reused, the purpose of defining {\tt free} is to detect accesses to non-allocated/previously allocated memory.
  */
  rule <k> (int *)malloc(N:Nat*sizeof(int)) => N':Nat <_/k>
       <ptr_> . => N' |-> N <_/ptr>    @latex("\\kBR")
       <mem_> . => N'..N' +Nat N |-> undef <_/mem> 
       <next> N' => N' +Int N </next>  
   [structural large]

  rule <k> free(N) => void <_/k> <ptr_> N |-> N' => . <_/ptr>
       <mem> Mem:Map => Mem[undef/N..N'+Nat N] </mem> [structural]
endkm

kmod KERNELC-CONSISTENT-MEMORY is including KERNELC-SEMANTICS 
  /*@ \section{Sequentially consistent memory access}

      The rules below specify atomic access to memory, for all three operations: read, write, and increment.
  */
  rule [deref]: <k> *N:Nat => V:Val <_/k> <mem_> N |-> V <_/mem>
  rule [increment]: <k> (*N)++ => I:Int <_/k> 
                    <mem_> N |-> (I => I +Int 1) <_/mem>
  rule [update]: <k> *N=V => V <_/k> 
                 <mem_> N |-> (_ => V) <_/mem>
endkm
