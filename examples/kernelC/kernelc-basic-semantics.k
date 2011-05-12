---(

require kernelc-syntax
---)
kmod KERNELC-BASIC-SEMANTICS is including KERNELC-DESUGARED-SYNTAX + K + PL-CONVERSION 
  syntax Val ::= Int | void 
  syntax Exp ::= Val 
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto] 
  syntax List{Exp} ::= List{Val} 
  syntax Nat ::= initialLoc
  syntax K ::= List{Exp} | List{PointerId} | List{DeclId} | StmtList | Pgm | String | initial | restore ( Map ) | increment ( Nat , Nat )
  syntax KResult ::= List{Val} 


  configuration <T ?> <k> .K </k> <env> .Map </env> <funs> .Map </funs> @latex("\\kBR")
                   <in> .List </in> <out> "" </out> <mem> .Map </mem> <ptr> .Map </ptr> 
                   <locks> .Map </locks> <next> initialLoc </next> </T ?> 
                <result ?> "" </result ?>


  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )
  rule run ( L:KLabel ) => <T_> <k> L(.List{K}) ~> '_`(`)(main) </k> <_/T> [structural]
  rule run ( L:KLabel , Il:List{K} ) => <T_> <k> L(.List{K}) ~> '_`(`)(main) </k> <in> List(Il) </in> <_/T> [structural]

  context *[HOLE]=_
  context (*[HOLE])++
  
  rule I1:Int == I2:Int => Bool2Int(I1 ==Int I2) [structural] 
  rule I1 != I2 =>  Bool2Int((I1 !=Int I2)) [structural]
  rule I1 + I2 => I1 +Int I2 [structural]
  rule I1 - I2 => _-Int_(I1,I2) [structural]
  rule I1 <= I2 => Bool2Int(I1 <=Int I2) [structural]
  rule '_?_:_ => 'if`(_`)_else_  [structural]
  rule if(I)_ else St:Stmt => St if I ==Int 0 [structural]
  rule if(I:Int) St else _ => St if notBool(I ==Int 0) [structural]
  rule V:Val ; => . [structural]
  rule <k> X:Id => V <_/k>  <env_> X |-> V <_/env> [structural]
  rule <k> X:Id ++ => I <_/k>  <env_> X |-> (I => I +Int 1) <_/env> [structural]
  rule <k> X = V => V <_/k> <env_> X |-> (_ => V) <_/env> [structural]
  rule <k> while(E:Exp) St => if (E) {St while(E) St} else {} <_/k> [structural]

  rule [print]: <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>
  rule [read-global]: <k> scanf("%d",N) => void <_/k> <mem_> N |-> (_ => I) <_/mem> <in> (ListItem(I) => .) <_/in>
  rule [read-local]: <k> scanf("%d",&X) => void <_/k> <env_> X |-> (_ => I) <_/env> <in> (ListItem(I) => .) <_/in>

---  rule #include<stdio.h> #include<stdlib.h> Sts:StmtList => Sts:StmtList 
---      [structural]
  rule {Sts:StmtList} => Sts  [structural]
  rule {} => .  [structural]
  rule St Sts => St ~> Sts [structural]


  rule <k> int X(Xl:List{DeclId}) {  Sts  return E ; } => . <_/k> 
       <funs_> . => X |-> int X(Xl:List{DeclId}) { Sts  return E ;} <_/funs> [structural]

  rule <k> '_`(_`)(X,,Vl:List{Val}) => Sts ~> E ~> restore(Env:Map) <_/k> 
       <env> Env => (eraseKLabel('int_,getList{K}(Xl)) |-> getList{K}(Vl)) </env>  @latex("\\kBR")
       <funs_> X |->  int X(Xl) { Sts  return E ;} <_/funs> [structural large]

  context int _ = [HOLE]
  rule <k> int X => void <_/k> <env_> . => (X |-> initial) <_/env> [structural]
 
  rule <k> V ~> (restore(Env) => .) <_/k> <env> _ => Env </env> [structural]

  rule 
     <k> (int *)malloc(N:Nat*sizeof(int)) => N':Nat <_/k>  <ptr_> . => N' |-> N <_/ptr> @latex("\\kBR")
       <mem_> . => N'..N' +Nat N |-> initial <_/mem> <next> N' => increment(N', N) </next>  
      
   [structural large]

  rule <k> free(N) => void <_/k> <ptr_> N |-> N' => . <_/ptr>
       <mem> Mem:Map => Mem[undef/N..N'+Nat N] </mem> [structural]


--- auxiliary functions
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N,,N1..N [structural]
endkm

kmod KERNELC-CONSISTENT-MEMORY is including KERNELC-BASIC-SEMANTICS 
  rule [deref]: <k> *N:Nat => V:Val <_/k> <mem_> N |-> V <_/mem>
  rule [increment]: <k> (*N)++ => I:Int <_/k> <mem_> N |-> (I => I +Int 1) <_/mem>
  rule [update]: <k> *N=V => V <_/k> <mem_> N |-> (_ => V) <_/mem>
endkm
