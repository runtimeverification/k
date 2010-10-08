kmod BASIC-KERNELC-SEMANTICS is including KERNELC-DESUGARED-SYNTAX + K + PL-CONVERSION 
  syntax Val ::= Int | void | & Id
  syntax Exp ::= Val 
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto] 
  syntax List{Exp} ::= List{Val} 
  syntax Nat ::= initialLoc
  syntax K ::= List{Exp} | List{PointerId} | List{DeclId} | StmtList | Pgm | String | initial | restore ( Map ) | increment ( Nat , Nat )
  syntax KResult ::= List{Val} 

  configuration <T> <threads> <thread*> <k> .K </k> <env> .Map </env> <id> 0 </id> </thread*> 
                    </threads> <cthreads> .Set </cthreads>
                    <funs> .Map </funs> <in> .List </in> <out> "" </out> 
                   <mem> .Map </mem> <ptr> .Map </ptr> 
                   <locks> .Map </locks> <next> initialLoc </next> </T> 
                <result> "" </result>
  context *[HOLE]=_
  
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
  rule <k> X = V => V <_/k> <env_> X |-> (_ => V) <_/env> [structural]
  rule <k> while(E:Exp) St => if (E) {St while(E) St} else {} <_/k> [structural]

  rule <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>
  rule <k> scanf("%d",N) => void <_/k> <mem_> N |-> (_ => I) <_/mem> <in> ListItem(I) => . <_/in>
  rule <k> scanf("%d",&X) => void <_/k> <env_> X |-> (_ => I) <_/env> <in> ListItem(I) => . <_/in>

---  rule #include<stdio.h> #include<stdlib.h> Sts:StmtList => Sts:StmtList 
---      [structural]
  rule {Sts:StmtList} => Sts  [structural]
  rule {} => .  [structural]
  rule St Sts => St ~> Sts [structural]

  rule <k> *N:Nat => V:Val <_/k> <mem_> N |-> V <_/mem>
  rule <k> *N=V => V <_/k> <mem_> N |-> (_ => V) <_/mem>

  rule <k> int X(Xl:List{DeclId}) {  Sts  return E ; } => . <_/k> 
       <funs_> . => X |-> int X(Xl:List{DeclId}) { Sts  return E ;} <_/funs> [structural]

  rule <k> '_`(_`)(X,,Vl:List{Val}) => Sts ~> E ~> restore(Env:Map) <_/k> 
       <env> Env => (eraseKLabel('int_,getList{K}(Xl)) |-> getList{K}(Vl)) </env>
       <funs_> X |->  int X(Xl) { Sts  return E ;} <_/funs> [structural]

  context int _ = [HOLE]
  rule <k> int X => 0 <_/k> <env_> . => (X |-> initial) <_/env>
  rule <k> int X = V => V <_/k> <env_> . => (X |-> V) <_/env>
 
  rule <k> V ~> (restore(Env) => .) <_/k> <env> _ => Env </env> [structural]

  rule <k> (int *)malloc(N:Nat*sizeof(int)) => N':Nat <_/k>  <ptr_> . => N' |-> N <_/ptr> 
       <mem_> . => N'..N' +Nat N |-> initial <_/mem> <next> N' => increment(N', N) </next> [structural]

  rule <k> free(N) => void <_/k> <ptr_> N |-> N' => . <_/ptr>
       <mem> Mem:Map => Mem[undef/N..N'+Nat N] </mem> [structural]

  context 'spawn_('_`(_`)(_,,`[HOLE`]:K)) 
  rule <k> 'spawn_('_`(_`)(X,,Vl)) => N <_/k> <next> N => increment(N,1) </next> (. => <thread_> <k>'_`(_`)(X,,Vl)</k> <id> N </id> <_/thread>) 
  rule (<thread_> <k> V </k> <id> N </id> <_/thread> => .) <cthreads_> . => SetItem(N) <_/cthreads> [structural]

  rule <k> join(N) => 0 <_/k> <cthreads_> SetItem(N) <_/cthreads> [structural]


  rule <k> acquire(N) => void <_/k> <id> N' </id> <locks_> N |-> (-1 => N') <_/locks>
  rule <k> release(N) => void <_/k> <id> N' </id> <locks_> N |-> (N' => -1) <_/locks>
  rule <k> acquire(N) => void <_/k> <id> N' </id> <locks> Locks:Map (. => N |-> N') </locks>
    if notBool(N in keys(Locks))


--- auxiliary functions
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N,,N1..N [structural]
endkm
