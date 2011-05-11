kmod PCF-UNTYPED-SEMANTICS is including PCF-UNTYPED-SYNTAX + K

  syntax K ::= Exp
  syntax KResult ::= Val

  configuration
    <T color="yellow">
      <k color="LightGreen"> .K </k>
      <env color="LightSkyBlue"> .Map </env>
      <store color="white"> .Map </store>
      <nextLoc color="gray"> 0 </nextLoc>
    </T>

  kvar L N : Nat
  kvar E E' : Exp
  kvar X : Id
  kvar V : Val

  //@ \textbf{Basic constructs}
  rule succ N => sNat(N)

  rule pred 0 => 0
  rule pred (sNat N) => N

  rule zero? 0 => true
  rule zero? (sNat N) => false

  rule cond true E E' => E
  rule cond false E E' => E'

  kvar Env Env' : Map

  //@ \textbf{Variable lookup}
  rule <k> X => E <_/k>
       <env_> X |-> L <_/env>
       <store_> L |-> E <_/store>

  //@ \textbf{$\lambda$-abstraction}
  syntax Val ::= closure-lambda ( Map , Id , Exp ) [latex "\textsf{closure}_\lambda({#1},{#2},{#3})"]
  rule <k> lambda X . E => closure-lambda(Env, X, E) <_/k>
       <env> Env </env> 

  rule <k> closure-lambda(Env, X, E) V => E ~> env(Env') <_/k>
       <env> Env' =>  Env[L / X] </env>
       <store_> . => L |-> V <_/store>
       <nextLoc> L => L +Nat 1 </nextLoc> 

  //@ \textbf{$\mu$-abstraction}
  syntax Exp ::= closure-mu ( Map , Exp ) [latex "\textsf{closure}_\mu({#1},{#2})"]
  rule <k> mu X . E => closure-mu(Env[L / X], E) <_/k>
       <env> Env </env>
       <store_> . => L |-> closure-mu(Env[L / X], E) <_/store>
       <nextLoc> L => L +Nat 1 </nextLoc> 

  rule <k> closure-mu(Env, E) => E ~> env(Env') <_/k>
       <env> Env' => Env </env> 

  //@ \textbf{Environment recovery}
  syntax K ::= env ( Map ) [latex "\textsf{env}({#1})"]
  rule <k> V ~> (env(Env) => .) <_/k>
       <env> _ => Env </env>
       [structural]

endkm
