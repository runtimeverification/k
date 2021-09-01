module IMP-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Ids    ::= List{Id, ","}

  syntax AExp   ::= Int | Id | String
                  | "-" Int
                  | "++" Id
                  | "read" "(" ")"
                  | "(" AExp ")" [bracket]
                  > AExp "/" AExp [strict, left, division]
                  > AExp "+" AExp [strict, left]

  syntax AExps  ::= List{AExp, ","}
                  | Ids

  syntax BExp   ::= Bool
                  | "!" BExp [strict]
                  | "(" BExp ")" [bracket]
                  | AExp "<=" AExp [seqstrict]
                  > BExp "&&" BExp [strict(1)]

  syntax Block  ::= "{" "}"
                  | "{" Stmt "}"

  syntax Stmt   ::= Block
                  | "halt" ";"
                  | "int" Ids ";"
                  | Id "=" AExp ";" [strict(2)]
                  | "if" "(" BExp ")" Block "else" Block [strict(1)]
                  | "while" "(" BExp ")" Block
                  | "print" "(" AExps ")" ";"
                  > "spawn" Stmt
                  > Stmt Stmt       [left]
endmodule

module IMP
  imports IMP-SYNTAX
  imports DOMAINS

  syntax KResult ::= Int | Bool | String

  configuration
    <T color="yellow">
      <threads color="orange">
        <thread multiplicity="*" color="blue" type="Set">
          <k color="green"> $PGM:Stmt </k>
          <env color="LightSkyBlue"> .Map </env>
        </thread>
      </threads>
      <store color="red"> .Map </store>
      <input color="magenta" stream="stdin"> .List </input>
      <output color="Orchid" stream="stdout"> .List </output>
    </T>

  // Exp

  rule  <k> X:Id => I ...</k>
        <env>... X |-> N ...</env>
        <store>... N |-> I ...</store>
        [lookup]

  rule  - I => 0 -Int I
  rule I1 / I2 => I1 /Int I2 requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule S1 + S2 => S1 +String S2

  rule  <k> ++ X => I +Int 1 ...</k>
        <env>... X |-> N ...</env>
        <store>... N |-> (I => I +Int 1) ...</store>
        [increment]

  rule ! B => notBool B
  rule I1 <= I2 => I1 <=Int I2
  rule true && B2 => B2
  rule false && _ => false

  // Stmt
  
  rule  <k> X:Id = I:Int ; => . ...</k>
        <env>... X |-> N ...</env>
        <store> S => S [N <- I] </store>
        [assignment]

  rule  <k> read() => I ...</k>
        <input> ListItem(I:Int) => .List ...</input>
        [read]

  context print(HOLE:AExp, _);

  syntax Printable  ::= Int | String
  syntax AExp       ::= Printable

  rule  <k> print(P:Printable, AEs => AEs) ; ...</k>
        <output>... .List => ListItem(P) </output>
        [print]

  rule  <k> print(.AExps) ; => . ...</k>

  rule  <k> if ( true  ) B else _ => B ...</k>
  rule  <k> if ( false ) _ else B => B ...</k>

  rule  <k> while (C) B => if (C) { B while (C) B } else { } ...</k>
        [structural]

  rule  <k> spawn S => . ...</k>
        <env> Rho </env>
        (.Bag =>
          <thread> 
            ...
            <k> S </k>
            <env> Rho </env>
            ...
          </thread>)

  rule  (<thread>... <k> . </k> ...</thread> => .Bag) [structural]

  rule  <k> halt ; ~> _ => . </k>

  rule  <k> S:Stmt S':Stmt => S ~> S' ...</k>

  // Block

  rule  <k> {   } => .        ...</k> [structural]
  rule  <k> { S } => S ~> Rho ...</k>
        <env> Rho </env> [structural]

  rule  <k> Rho => . ...</k>
        <env> _ => Rho </env> [structural]

  // Pgm

  rule  <k> int (X, Xs => Xs) ;  ...</k>
        <env> Rho => Rho [X <- !N:Int] </env>
        <store>... .Map => !N |-> 0 ...</store>

  rule  <k> int .Ids ; => . ...</k>
endmodule
