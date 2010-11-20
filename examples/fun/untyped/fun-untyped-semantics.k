kmod FUN-UNTYPED-SEMANTICS is including FUN-DESUGARED-SYNTAX + K
  syntax Val ::= Int | Bool
  syntax Exp ::= Val
  syntax K ::= List{Exp}
  syntax KResult ::= List{Val}

  configuration <T>  <k> .K </k>
                     <env> .Map </env>
                     <store> .Map </store>
                     <nextLoc> 0 </nextLoc>
                </T>

  rule <k> X:Id => V:Val <_/k> <env_> X|->L:Nat <_/env> <store_> L|->V <_/store>
  rule I1:Int + I2:Int => I1 +Int I2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 if I2 =/=Bool 0
  rule - I:Int => -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==Bool V2
  rule V1 != V2 => V1 =/=Bool V2
  rule T1:Bool and T2:Bool => T1 andBool T2
  rule T1 or T2 => T1 orBool T2
  rule not(T:Bool) => notBool(T)
  syntax Val ::= closure ( Map , List{Id} , Exp )
  rule <k> fun Xl:List{Id} -> E:Exp => closure(Env:Map,Xl,E) <_/k> <env> Env </env> 
  rule <k> closure(Env,Xl,E) Vl:List{Val} => Vl ~> bindTo(Xl) ~> E ~> env(Env') <_/k> <env> Env':Map => Env </env>
  rule <k> let Xl = El:List{Exp} in E => El ~> bindTo(Xl) ~> E ~> env(Env) <_/k> <env> Env </env>
  rule <k> letrec Xl = El in E => bindTo(Xl) ~> El ~> writeTo(Xl) ~> E ~> env(Env) <_/k> <env> Env </env>
  syntax Val ::= cc ( Map , K )
  rule <k> (callcc V => V cc(Env,K)) ~> K </k> <env> Env </env> 
  rule <k> cc(Env,K:K) V ~> _ => V ~> K </k> <env> _ => Env </env> 
  rule if  true then E else _ => E
  rule if false then _ else E => E 
  rule car [V,_:List{Val}] => V
  rule cdr [_:Val,Vl] => [Vl]
  rule null? [()] => true
  rule null? [_:Val,_:List{Val}] => false
  rule cons V [Vl] => [V,Vl]
  rule <k> ref V => L <_/k> <store_> . => L|->V <_/store> <nextLoc> L => sNat L </nextLoc>
  rule <k> &X => L <_/k> <env_> X|->L <_/env>
  rule <k> *L => V <_/k> <store_> L|->V <_/store>
  rule <k> L:=V => V  <_/k> <store_> L|->(_=>V) <_/store>
  rule V1; V2 => V2

----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------
--- List{Val}
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- Environment recovery
  syntax K ::= env ( Map )
  rule (env(_) => .) ~> env(_)                                         [structural]    --- tail recursion
  rule <k> env(Env) => . <_/k> <env> _ => Env </env>                   [structural]
  rule <k> V ~> (env(Env) => .) <_/k> <env> _ => Env </env>            [structural]

--- bindTo and writeTo
  syntax K ::= bindTo List{Id} | writeTo List{Id}
  rule <k> () ~> bindTo() => . <_/k>                                   [structural]
  rule <k> ((V=>()),_:List{Val}) ~> bindTo((X=>()),_:List{Id}) <_/k>
       <env> Env => Env[N/X] </env>
       <store_> .Map => N|->V <_/store>
       <nextLoc> N:Nat => sNat N </nextLoc>  if X =/=Bool ()           [structural]

  rule <k> bindTo() => . <_/k>                                         [structural]
  rule <k> bindTo((X=>()),_:List{Id}) <_/k>
       <env> Env => Env[N/X] </env>
       <nextLoc> N => sNat N </nextLoc>  if X =/=Bool ()               [structural]

  rule <k> () ~> writeTo() => . <_/k>                                  [structural]
  rule <k> ((V=>()),_:List{Val}) ~> writeTo((X=>()),_:List{Id}) <_/k>
          <env_> X|->L <_/env> <store_> . => L|->V <_/store>           [structural]
endkm
