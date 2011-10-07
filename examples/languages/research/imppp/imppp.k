require /modules/uris

module IMPPP-SYNTAX
  syntax AExp ::= #Int | #Id
                | AExp + AExp [gather(E e) prec 33 strict]
                | AExp / AExp [gather(E e) prec 31 strict]
                | ++ #Id [prec 0]
                | read ( )
                | exchange ( AExp ) [strict]

  syntax BExp ::= #Bool
                | AExp <= AExp [prec 37 latex "{#1}\leq{#2}" seqstrict]
                | not BExp [prec 53 strict]
                | BExp and BExp [gather(E e) prec 55 strict(1)]

  syntax Stmt ::= skip
                | #Id := AExp  [prec 80 gather (e E) strict(2)]
                | Stmt ; Stmt [prec 100 gather(e E)]
                | if BExp then Stmt else Stmt [strict(1)]
                | while BExp do Stmt
                | print ( PExp )  [strict]
                | halt
                | spawn Stmt [prec 90]
                | { }
                | { Stmt } [gather(&)]
                | var Ids [prec 70]

  syntax Ids ::= List{#Id,","}
  syntax PExp ::= AExp | #String 
end module

module IMPPP imports IMPPP-SYNTAX + URIS
  syntax KResult ::= #Bool | #Int | #String

  configuration
    <T color="yellow">
      <threads color="orange">
        <thread multiplicity="*" color="red">
          <k color="green">$PGM:K</k>
          <env color="LightSkyBlue">.Map</env>
        </thread>
     </threads>
     <br/>
     <store color="white">.Map</store>
     <nextLoc color="gray">0</nextLoc>
     <in color="magenta" stream="stdin">.List</in>
     <out color="Orchid" stream="stdout">.List</out>
    </T>

  /*@ \textbf{Variable lookup} */
  rule <k> X:#Id => I ...</k>
       <env>... X |-> N:#Nat ...</env>
       <store>... N |-> I:#Int ...</store> [transition]

  /*@ \textbf{Arithmetic expressions} */
  rule I1:#Int + I2:#Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0

  /*@ \textbf{Variable increment} */
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store> [transition]

  /*@ \textbf{Input} */
  rule <k> read() => I ...</k>
       <in> ListItem(I) => . ...</in> [transition]

  /*@ \textbf{Exchange synchronization construct} */

  rule <k> exchange(I1) => I2 ...</k> <k> exchange(I2) => I1 ...</k> [transition]

  /*@ \textbf{Boolean expressions} */
  rule I1 <= I2 => I1 <=Int I2
  rule not T:#Bool => notBool T
  rule true and B:BExp => B
  rule false and B => false

  rule skip => .

  /*@ \textbf{Variable assignment} */
  rule <k> X := I => . ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>

   /*@ \textbf{Statement sequentialization} */
  rule S1:Stmt ; S2:Stmt => S1 ~> S2

 /*@ \textbf{Conditional} */
  rule if  true then S1 else _  => S1
  rule if false then _  else S2 => S2

  /*@ \textbf{While loop} */
  rule <k> while B do S:Stmt => if B then S ; while B do S else {} ...</k>

  /*@ \textbf{Output} */
  rule <k> print(I) => . ...</k>
       <out>... . => ListItem(I) </out>
  rule <k> print(Str:#String) => . ...</k>
       <out>... . => ListItem(Str) </out>

  /*@ \textbf{Halt} */
  rule <threads>... <k> halt ...</k> ...</threads> => .

  /*@ \textbf{Spawn thread} */
  rule <k> spawn S => . ...</k>
       <env> Rho </env>
       (. => <thread>... <k> S </k> <env> Rho </env> ...</thread>)

  /*@ \textbf{Dissolve thread} */
  rule <thread>... <k> .K </k> ...</thread> => .

  /*@ \textbf{Block} */
  rule {} => .
  rule <k> {S} => S ~> env(Rho) ...</k>
       <env> Rho:Map </env>

  /*@ \textbf{Variable declaration} */
  rule <k> var (X,Xl => Xl:List{#Id,","}) ...</k>
       <env> Rho => Rho[N/X] </env> 
       <store>... . => N |-> 0 ...</store>
       <nextLoc> N => sNat N </nextLoc>

  rule var .List{","} => .


  /*@ \textbf{Environment recovery} */
  syntax K ::= env Map
  rule env(_) ~> env(Rho) => env(Rho) [structural]
  rule <k> env(Rho) => . ...</k> <env> _ => Rho </env> [structural]
end module
