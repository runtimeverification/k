// 30 semantic rules
// 16 syntax translation macros
kmod KERNELC-SEMANTICS is 
  including K
  including KERNELC-DESUGARED-SYNTAX + PL-CONVERSION + PL-RANDOM

/*@ \section{\KERNELC semantics}
This module describes the basic configuration and semantics for the 
\KERNELC language.  The semantics contains 30 semantic rules and 16 
translation macros.  */

/*@ \subsection{Configuration}
The basic configuration for \KERNELC contains a computation cell {\sf k}, 
an environment cell mapping (local) variables to values, a function stack 
cell for  saving the control context upon calling a function, input and 
output cells, a memory cell mapping location (represented as naturals) to 
values (integers), a {\sf ptr} cell for maintaining information about 
memory blocks allocation sizes,  a counter for generating fresh locations 
and integers, and a {\sf rand} cell to help in the random number 
generation process.  */

  configuration 
  <T multiplicity="?"> 
      <k color="green"> .K </k> 
      <env color="yellow"> .Map </env> 
      <funs color="ForestGreen"> .Map </funs>            <br/>
      <fstack color="LawnGreen"> .List </fstack>
      <in color="magenta"> .List </in> 
      <out color="Fuchsia"> "" </out> 
      <mem color="orange"> .Map </mem> 
      <ptr color="OrangeRed"> .Map </ptr> 
      <next> 0 </next> 
      <rand> 0 </rand>
  </T> 
  <result multiplicity="?"> "" </result>

//@ \subsection{Arithmetic expressions}

  rule I1 + I2 => I1 +Int I2 [structural]
  rule I1 - I2 => _-Int_(I1,I2) [structural]
  rule I1 % I2 => I1 %Int I2 if I2 !=Int 0 [structural]
  rule I1 <= I2 => Bool2Int(I1 <=Int I2) [structural]
  rule I1 < I2 => Bool2Int(I1 <Int I2) [structural]
  rule I1:Int == I2:Int => Bool2Int(I1 ==Int I2) [structural] 
  rule I1 != I2 =>  Bool2Int((I1 !=Int I2)) [structural]

//@ Expression conditional is desugared into the statement conditional.

  rule '_?_:_ => 'if`(_`)_else_  [structural]

/*@ \subsection{Variable declaration}
Newly declared variables are mapped in the environment to the special 
{\tt undef} computation constant which is not a value and thus it 
cannot be read. */

  syntax K ::= undef
  context int _ = [HOLE]
  rule <k> int X => void <_/k> 
       <env> Env => Env[undef / X] <_/env> 
  [structural]
 
/*@ \subsection{Operations on local variables}
Local variables in \KERNELC are restricted.  They cannot be shared, 
cannot be addressed, and therefore reside in a separate space called 
the environment.

Since their behavior does not depend on the interaction of threads, 
accesses to them are considered structural when analyzing thread 
interactions.  */

  rule <k> X:Id => V <_/k>       <env_> X |-> V <_/env>    [structural]
  rule <k> X:Id ++ => I <_/k>    <env_> X |-> (I => I +Int 1) <_/env> 
  [structural]
  rule <k> X = V => V <_/k>      <env_> X |-> (_ => V) <_/env> [structural]

/*@ \subsection{Operations on heap variables}
A very basic semantics for allocating and freeing memory is defined in 
the {\tt KERNELC-SIMPLE-MALLOC} module.
    
A sequentially consistent semantics for accessing the heap is defined 
in the {\tt KERNELC-CONSISTENT-MEMORY} module.  

We give here only the strictness constraints for evaluating a pointer 
dereference expression to an l-value, as these are independent of the 
allocator/memory model. */
 
  context *[HOLE]=_
  context (*[HOLE])++
  

//@ \subsection{User-declared Functions}

/*@ \subsubsection{Function declaration}
Upon meeting a function declaration, the function is simply saved in the 
map of functions.  */

  rule <k> __`{_`}(int F:Id, Xl:List{DeclId}, Sts) => . <_/k> 
       <funs_> . => F |-> int F(Xl) { Sts } <_/funs> 
  [structural]

/*@ Moreover we desugar void functions into integer functions returning 
the special value {\tt void} to avoid special casing the latter. */

  rule __`{_`}((void_(F) => int_(F)), Xl:List{DeclId}, 
               (Sts => __(Sts, return void;))) 
  [structural]

/*@ \subsubsection{Function invocation and return}
When calling a function, a triple is pushed on the function stack, 
consisting of the name of the function, the current environment and the 
remainder of the computation.  Then the current computation is replaced 
by the body of the function, the environment by the mapping of the 
arguments to their passed values.  When returning, the environment and 
computation are restored with the function call being replaced by the 
return value.

The reason for pushing the name of the function on the function stack is 
for analysis purposes; it effectively exposes the call stack for 
debugging, monitoring and trace checking purposes. */

  syntax ListItem ::=  Id # Map # K 

  rule <k> '_`(_`)(F,,Vl:List{Val}) ~> K => Sts </k> 
    <env> Env => (eraseKLabel('int_,getList{K}(Xl)) |-> getList{K}(Vl)) </env>
    <br/>    
    <funs_> F |->  int F(Xl) { Sts } <_/funs> 
    <fstack> . => F # Env:Map # K:K <_/fstack>
  [structural large]

  rule <k> return V ; ~> _ => V ~> K </k> <env> _ => Env </env> 
       <fstack> _ # Env # K => . <_/fstack> 
  [structural]

//@ \subsection{Statements}

  rule {} => .  [structural]

/*@ When giving the semantics of the block statement we save the 
environment on the computation stack to be recovered upon finishing 
executing the statements in the block. */
  
  syntax K ::= env ( Map )
  rule <k> {Sts:StmtList} => Sts ~> env(Env) <_/k> <env> Env </env>
  [structural]
  rule <k> env(Env) => . <_/k> <env> _ => Env </env> [structural]
  rule V:Val ; => . [structural]
  rule St Sts => St ~> Sts [structural]

/*@ \subsubsection{Conditional and loop}
The semantics of the conditional is on purpose given by using 
constraints on the condition value expressed as side conditions instead 
of direct matching.  The reason for this is to allow extending the 
semantics to handle execution in the presence of symbolic pointer values. */

  rule if(I)_ else St:Stmt => St if I ==Int 0 [structural]
  rule if(I:Int) St else _ => St if notBool(I ==Int 0) [structural]
  rule <k> while(E:Exp) St => if (E) {St while(E) St} else {} <_/k> 
  [structural]

//@ \subsection{Additional Library Functions}

/*@ \subsubsection{Input/Output}
These are proper rules as order interaction with the input/output channels
is important for thread interaction.

We chose here to give the semantics of reading input data into the memory
through an assignment to allow potential interleavings between the action 
of reading from the input buffer and that of writing into memory.  To 
contrast that, we make reading of input data into a local variable atomic, 
as local variables have no concurrency role. */

  syntax K ::= String
  rule [print]: <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>
  rule [read-global]: <k> scanf("%d",N:Nat) => (*N) = I <_/k> 
       <in> (ListItem(I) => .) <_/in>
  rule [read-local]: <k> scanf("%d",&X) => I <_/k> 
       <in> (ListItem(I) => .) <_/in> 
       <env_> X |-> (_ => I) <_/env>

/*@ \subsubsection{Random}
The semantics of rand is given through the Maude built-in Mersenne Twister 
Random Number Generator algorithm which is exposed by the 
{\tt randomRandom} function provided in the {\tt PL-RANDOM} module which 
gives the Nth number in the Mersene Twister sequence.

As initializing the seed for the Mersenne twister is done in Maude at 
invocation time, srand currently has the same semantics independent of 
the provided seed. */

  rule <k> rand() => randomRandom(N) <_/k>
       <rand> N:Nat => N +Nat 1 </rand>

  rule <k> srand(I) => void <_/k>

//@ \subsection{Auxiliary declaration and helping constructs}
  
//@ \subsubsection{Value declarations}

  syntax Val ::= Int | void 
  syntax Exp ::= Val 
  syntax KResult ::= List{Val} 

  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto] 
  syntax List{Exp} ::= List{Val} 

//@ \subsubsection{Generating sequences of numbers}

  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N,,N1..N [structural]
endkm

kmod KERNELC-SIMPLE-MALLOC is including KERNELC-SEMANTICS
/*@ \section{A simple memory allocator} 
The rules below define a very simple memory allocation mechanism, which
basically allocates memory in order, starting with the location 
following the last allocated location.  Since the memory is not reused,
the purpose of defining {\tt free} is to detect accesses to 
non-allocated/previously allocated memory.  */

  rule <k> (int *)malloc(N:Nat*sizeof(int)) => N':Nat <_/k>
       <ptr_> . => N' |-> N <_/ptr>    <br/>
       <mem_> . => N'..N' +Nat N |-> undef <_/mem> 
       <next> N' => N' +Int N </next>  
   [structural large]

  rule <k> free(N) => void <_/k> <ptr_> N |-> N' => . <_/ptr>
       <mem> Mem:Map => Mem[undef/N..N'+Nat N] </mem> 
   [structural]
endkm

kmod KERNELC-CONSISTENT-MEMORY is including KERNELC-SEMANTICS 
/*@ \section{Sequentially consistent memory access}
The rules below specify atomic access to memory, for all three 
operations: read, write, and increment. */
  rule [deref]: <k> *N:Nat => V:Val <_/k> <mem_> N |-> V <_/mem>
  rule [increment]: <k> (*N)++ => I:Int <_/k> 
                    <mem_> N |-> (I => I +Int 1) <_/mem>
  rule [update]: <k> *N=V => V <_/k> 
                 <mem_> N |-> (_ => V) <_/mem>
endkm
