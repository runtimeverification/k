kmod EXP-UNTYPED-SEMANTICS is including EXP-UNTYPED-DESUGARED-SYNTAX + K 

  syntax Val ::= #Int | #Bool
  syntax Exp ::= Val
  syntax K ::= Exp
  syntax KResult ::= Val

  configuration <T>  <k> .K </k>
                     <env> .Map </env>
                     <store> .Map </store>
                     <nextLoc> 0 </nextLoc>
                </T>

  rule <k> X:#Id => E:Exp <_/k> <env_> X |-> L:#Nat <_/env> <store_> L |-> E <_/store>
  rule I1:#Int + I2:#Int => I1 +Int I2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 if I2 =/=Bool 0
  rule - I:#Int => -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==Bool V2
  rule V1 != V2 => V1 =/=Bool V2
  rule T1:#Bool and T2:#Bool => T1 andBool T2
  rule T1 or T2 => T1 orBool T2
  rule not(T:#Bool) => notBool(T)
  rule if  true then E else  _  => E
  rule if false then  _  else E => E
  syntax Val ::= closure-lambda ( Map , #Id , Exp ) [latex "\textsf{closure}_\lambda({#1},{#2},{#3})"]
  rule <k> lambda X . E => closure-lambda(Env:Map,X,E) <_/k> <env> Env </env> 
  rule <k> closure-lambda(Env,X,E) V:Val => E ~> env(Env') <_/k> <env> Env':Map =>  Env[L/X] </env>
          <store_> . => L|->V <_/store> <nextLoc> L => sNat L </nextLoc> 
  syntax Exp ::= closure-mu ( Map , Exp ) [latex "\textsf{closure}_\mu({#1},{#2})"]
  rule <k> mu X . E => closure-mu(Env[L/X],E) <_/k> <env> Env </env>
          <store_> . => L |-> closure-mu(Env[L/X],E) <_/store> <nextLoc> L => sNat L </nextLoc> 
  rule <k> closure-mu(Env,E) => E ~> env(Env') <_/k> <env> Env' => Env </env> 

---(
--- we need mu closures ... the rule below is wrong, because the free variables
--- of E can be captured ... nastily ... argh; see p12
  rule <k> mu X . E => E ~> env(Env) <_/k> <env> Env => Env[L/X] </env>
          <store_> . => L |-> mu X . E <_/store> <nextLoc> L => sNat L </nextLoc> 
---)

----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------
  syntax K ::= env ( Map )                                                --- Environment recovery
  rule <k> V ~> (env(Env) => .) <_/k> <env> _=>Env </env> [structural]
  rule (env(_) => .) ~> env(_)                            [structural]    --- Tail recursion
endkm
