module IMP-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Ids    ::= List{Id, ","}

  syntax AExp   ::= Int | Id
                  | "-" Int
                  | "(" AExp ")" [bracket]
                  > AExp "/" AExp [strict]
                  > AExp "+" AExp [strict, left]

  syntax BExp   ::= Bool
                  | "!" BExp [strict]
                  | "(" BExp ")" [bracket]
                  | AExp "<=" AExp [seqstrict]
                  > BExp "&&" BExp [strict(1)]

  syntax EmptyBlock ::= "{" "}"

  syntax Block  ::= EmptyBlock
                  | "{" Stmt "}"

  syntax Stmt   ::= Block
                  | Id "=" AExp ";" [strict(2)]
                  | "if" "(" BExp ")" Block "else" Block [strict(1)]
                  | "while" "(" BExp ")" Block
                  > Stmt Stmt       [seqstrict]

  syntax Pgm    ::= "int" Ids ";" Stmt
endmodule

module IMP
  imports IMP-SYNTAX
  imports DOMAINS

  syntax KResult ::= Int | Bool | EmptyBlock

  configuration
    <T color="yellow">
      <k color="green"> $PGM:Pgm </k>
      <state color="red"> .Map </state>
    </T>

  // Exp

  rule  <k> X:Id => I ...</k>
        <state>... X |-> I ...</state>

  rule  - I => 0 -Int I
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2

  rule ! B => notBool B
  rule I1 <= I2 => I1 <=Int I2
  rule true && B2 => B2
  rule false && _ => false

  // Stmt
  
  rule  <k> X:Id = I:Int ; => { } ...</k>
        <state> S => S[X <- I] </state>
        requires X in_keys(S)

  rule  <k> if ( true  ) B else _ => B ...</k>
  rule  <k> if ( false ) _ else B => B ...</k>

  rule  <k> while (C) B => if (C) { B while (C) B } else { } ...</k>
        [structural]

  rule  <k> { } S':Stmt => S' ...</k>

  // Block

  rule  <k> { S } => S ...</k> [structural]

  // Pgm

  rule  <k> int (X, Xs => Xs) ; _  ...</k>
        <state> S => S[X <- 0] </state>
        requires notBool X in_keys(S)

  rule  <k> int .Ids ; S => S ...</k>
endmodule
