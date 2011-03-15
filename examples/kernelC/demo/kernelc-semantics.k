--- 30 semantic rules
--- 16 syntax translation macros
kmod KERNELC-SEMANTICS is 
  including KERNELC-DESUGARED-SYNTAX + K + PL-CONVERSION + PL-RANDOM

  configuration 
  <T multiplicity="?"> 
      <k> .K </k> 
      <env> .Map </env> 
      <funs> .Map </funs>               @latex("\\kBR")
      <fstack> .List </fstack>
      <in> .List </in> 
      <out> "" </out> 
      <mem> .Map </mem> 
      <ptr> .Map </ptr> 
      <next> 0 </next> 
      <rand> 0 </rand>
  </T> 
  <result multiplicity="?"> "" </result>

  --- operations on local variables
  rule <k> X:Id => V <_/k>       <env_> X |-> V <_/env>    [structural]
  rule <k> X:Id ++ => I <_/k>    <env_> X |-> (I => I +Int 1) <_/env> 
  [structural]
  rule <k> X = V => V <_/k>      <env_> X |-> (_ => V) <_/env> [structural]


 --- arithmentic expressions
  rule I1 + I2 => I1 +Int I2 [structural]
  rule I1 - I2 => _-Int_(I1,I2) [structural]
  rule I1 % I2 => I1 %Int I2 if I2 !=Int 0 [structural]
  rule I1 <= I2 => Bool2Int(I1 <=Int I2) [structural]
  rule I1 < I2 => Bool2Int(I1 <Int I2) [structural]
  rule I1:Int == I2:Int => Bool2Int(I1 ==Int I2) [structural] 
  rule I1 != I2 =>  Bool2Int((I1 !=Int I2)) [structural]
  rule '_?_:_ => 'if`(_`)_else_  [structural]

  --- conditional and loop
  rule if(I)_ else St:Stmt => St if I ==Int 0 [structural]
  rule if(I:Int) St else _ => St if notBool(I ==Int 0) [structural]
  rule <k> while(E:Exp) St => if (E) {St while(E) St} else {} <_/k> 
  [structural]


  --- input/output
  rule [print]: <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>
  rule [read-global]: <k> scanf("%d",N) => void <_/k> <mem_> N |-> (_ => I) <_/mem> <in> (ListItem(I) => .) <_/in>
  rule [read-local]: <k> scanf("%d",&X) => void <_/k> <env_> X |-> (_ => I) <_/env> <in> (ListItem(I) => .) <_/in>

  --- basic statements
  rule V:Val ; => . [structural]
  rule {Sts:StmtList} => Sts  [structural]
  rule {} => .  [structural]
  rule St Sts => St ~> Sts [structural]


  --- function declaration and function call
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

  rule <k> (int *)malloc(N:Nat*sizeof(int)) => N':Nat <_/k>
       <ptr_> . => N' |-> N <_/ptr>    @latex("\\kBR")
       <mem_> . => N'..N' +Nat N |-> undef <_/mem> 
       <next> N' => N' +Int N </next>  
   [structural large]

  rule <k> free(N) => void <_/k> <ptr_> N |-> N' => . <_/ptr>
       <mem> Mem:Map => Mem[undef/N..N'+Nat N] </mem> [structural]


  rule <k> random() => randomRandom(N') <_/k>
       <rand> N' => N' +Nat 1 </rand>

  rule <k> srandom(I) => void <_/k>

  context *[HOLE]=_
  context (*[HOLE])++
  
  syntax Val ::= Int | void 
  syntax Exp ::= Val 
  syntax K ::= List{Exp} | List{PointerId} | List{DeclId} | StmtList | Pgm | String | undef | restore ( Map ) 
  syntax KResult ::= List{Val} 


--- auxiliary functions
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N,,N1..N [structural]

  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto] 
  syntax List{Exp} ::= List{Val} 
endkm

kmod KERNELC-CONSISTENT-MEMORY is including KERNELC-SEMANTICS 
  rule [deref]: <k> *N:Nat => V:Val <_/k> <mem_> N |-> V <_/mem>
  rule [increment]: <k> (*N)++ => I:Int <_/k> 
                    <mem_> N |-> (I => I +Int 1) <_/mem>
  rule [update]: <k> *N=V => V <_/k> 
                 <mem_> N |-> (_ => V) <_/mem>
endkm
