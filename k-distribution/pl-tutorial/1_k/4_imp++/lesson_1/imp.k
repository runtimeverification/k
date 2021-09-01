module IMP-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Ids    ::= List{Id, ","}

  syntax AExp   ::= Int | Id | String
                  | "-" Int
                  | "++" Id
                  | read()
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

  syntax KResult ::= Int | Bool

  configuration
    <T color="yellow">
      <k color="green"> $PGM:Stmt </k>
      <state color="red"> .Map </state>
    </T>

  // Exp

  rule  <k> X:Id => I ...</k>
        <state>... X |-> I ...</state>

  rule  - I => 0 -Int I
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2

  /* rule  <k> ++ X:Id => X = X + 1 ; ~> X ...</k> */

  rule ! B => notBool B
  rule I1 <= I2 => I1 <=Int I2
  rule true && B2 => B2
  rule false && _ => false

  // Stmt
  
  rule  <k> X:Id = I:Int ; => . ...</k>
        <state> S => S[X <- I] </state>
        requires X in_keys(S)

  rule  <k> if ( true  ) B else _ => B ...</k>
  rule  <k> if ( false ) _ else B => B ...</k>

  rule  <k> while (C) B => if (C) { B while (C) B } else { } ...</k>
        [structural]

  rule  <k> S:Stmt S':Stmt => S ~> S' ...</k>

  // Block

  rule  <k> {   } => . ...</k> [structural]
  rule  <k> { S } => S ...</k> [structural]

  // Pgm

  rule  <k> int (X, Xs => Xs) ;  ...</k>
        <state> S => S[X <- 0] </state>
        requires notBool X in_keys(S)

  rule  <k> int .Ids ; => . ...</k>
endmodule
