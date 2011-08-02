in imppp-syntax
in imppp-programs

kmod IMPPP-CONFIGURATION is including IMPPP-SYNTAX + K
  syntax K ::= AExp | BExp | Stmt
  syntax KResult ::= #Bool | #Int

  configuration
    <T color="yellow">
      <threads color="orange">
        <thread multiplicity="*" color="red">
          <k color="green">.K</k>
          <env color="LightSkyBlue">.Map</env>
        </thread>
     </threads>
     <br/>
     <store color="white">.Map</store>
     <nextLoc color="gray">0</nextLoc>
     <in color="magenta">.List</in>
     <out color="Orchid">.List</out>
    </T>
endkm

kmod IMPPP-SEMANTICS is including IMPPP-CONFIGURATION
  /*@ \textbf{Variable lookup} */
  rule <k> X:#Id => I <_/k>
       <env_> X |-> N:#Nat <_/env>
       <store_> N |-> I:#Int <_/store>

  /*@ \textbf{Arithmetic expressions} */
  rule I1:#Int + I2:#Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0

  /*@ \textbf{Variable increment} */
  rule <k> ++X => I +Int 1 <_/k>
       <env_> X |-> N <_/env>
       <store_> N |-> (I => I +Int 1) <_/store>

  /*@ \textbf{Input} */
  rule <k> read => I <_/k>
       <in> ListItem(I) => . <_/in>

  /*@ \textbf{Boolean expressions} */
  rule I1 <= I2 => I1 <=Int I2
  rule not T:#Bool => notBool T
  rule true and B:BExp => B
  rule false and B => false

  /*@ \textbf{Statement sequentialization} */
  rule {} => .
  rule I; => .
  rule S1:Stmt S2:Stmt => S1 ~> S2

  /*@ \textbf{Variable assignment} */
  rule <k> X = I; => . <_/k>
       <env_> X |-> N <_/env>
       <store_> N |-> (_ => I) <_/store>

  /*@ \textbf{Conditional} */
  rule if  true then S1 else _  => S1
  rule if false then _  else S2 => S2

  /*@ \textbf{While loop} */
  rule <k> while B do S:Stmt => if B then S while B do S else {} <_/k>

  /*@ \textbf{Output} */
  rule <k> print I; => . <_/k>
       <out_> . => ListItem(I) </out>

  /*@ \textbf{Spawn thread} */
  rule <k> spawn S => . <_/k>
       <env> Rho </env>
       (. => <thread_> <k> S </k> <env> Rho </env> <_/thread>)

  /*@ \textbf{Dissolve thread} */
  rule <thread_> <k> .K </k> <_/thread> => .

  /*@ \textbf{Halt thread} */
  rule <k> haltThread; ~> _ => .</k>

  /*@ \textbf{Variable declaration} */
  rule <k> var X; => . <_/k>
       <env> Rho => Rho[N/X] </env> 
       <store_> . => N |-> 0 <_/store>
       <nextLoc> N => sNat N </nextLoc>

  /*@ \textbf{Block} */
  rule <k> {S} => S ~> env(Rho) <_/k>
       <env> Rho:Map </env>

  /*@ \textbf{Environment recovery} */
  syntax K ::= env Map
  rule env(_) ~> env(Rho) => env(Rho) [structural]
  rule <k> env(Rho) => . <_/k> <env> _ => Rho </env> [structural]
endkm

kmod IMPPP is including IMPPP-SEMANTICS + IMPPP-PROGRAMS 
  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )
  rule run(KL:KLabel) => run(KL,.List{K}) [structural]
  rule run(KL,L:List`{K`}) => <T_> <k> KL(.List{K}) </k> <in> List(L) </in> <_/T> [structural]
endkm
