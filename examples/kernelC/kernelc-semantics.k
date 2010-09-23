
kmod KERNELC-SEMANTICS is including KERNELC-DESUGARED-SYNTAX + K + PL-CONVERSION 
  syntax Val ::= Int | void 
  syntax Exp ::= Val 
  syntax K ::= Exp | StmtList | Pgm | String
  syntax KResult ::= Val 

  configuration <T> <k> .K </k> <env> .Map </env> <mem> .Map </mem> <ptr> .Map </ptr>
                    <next> 1 </next> <out> "" </out> </T>
  context *[HOLE]=_
  
  rule I1:Int == I2:Int => Bool2Int(I1 ==Int I2)
  rule I1 != I2 =>  _-Int_(I1,I2)
  rule I1 + I2 => I1 +Int I2 
  rule I1 - I2 => _-Int_(I1,I2)
  rule I1 <= I2 => Bool2Int(I1 <=Int I2)
  rule '_?_:_ => 'if`(_`)_else_  [structural]
  rule if(I)_ else St:Stmt => St if I ==Int 0
  rule if(I:Int) St else _ => St if I !=Int 0
  rule V:Val ; => .
  rule <k> X:Id => V <_/k>  <env_> X |-> V <_/env> 
  rule <k> X = V => V <_/k> <env> Env:Map => Env[V/X] </env>
  rule <k> *N:Nat => V <_/k> <mem_> N |-> V <_/mem>
  rule <k> *N=V => V <_/k> <mem_> N |-> (_ => V) <_/mem>
  rule <k> while(E:Exp) St => if (E) {St while(E) St} else ; <_/k>
  rule <k> malloc(N) => N':Nat <_/k>  <ptr_> . => N' |-> N <_/ptr> 
       <mem_> . => N'..N' +Nat N |-> 0 <_/mem> <next> N' => N' +Nat N </next>

  rule <k> free(N) => void <_/k> <ptr_> N |-> N' => . <_/ptr>
       <mem> Mem:Map => Mem[undef/N..N'+Nat N] </mem> 

  rule <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>

  
  rule #include<stdio.h> #include<stdlib.h> void main(void) {Sts:StmtList} => Sts:StmtList 
      [structural]
  rule ; => .
  rule {Sts} => Sts  [structural]
  rule St Sts => St ~> Sts

--- auxiliary functions
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..N2:Nat => N1,,sNat N1..N2 [structural]
endkm
