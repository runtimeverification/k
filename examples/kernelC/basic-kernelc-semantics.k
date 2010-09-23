
kmod BASIC-KERNELC-SEMANTICS is including KERNELC-DESUGARED-SYNTAX + K + PL-CONVERSION 
  syntax Val ::= Int | void 
  syntax Exp ::= Val 
  syntax K ::= Exp | StmtList | Pgm | String
  syntax KResult ::= Val 

  configuration <T> <k> .K </k> <env> .Map </env> <out> "" </out> </T>
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
  rule <k> while(E:Exp) St => if (E) {St while(E) St} else ; <_/k>

  rule <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>

  rule #include<stdio.h> #include<stdlib.h> void main(void) {Sts:StmtList} => Sts:StmtList 
      [structural]
  rule ; => .
  rule {Sts} => Sts  [structural]
  rule St Sts => St ~> Sts
endkm
