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

  syntax Block  ::= "{" "}"
                  | "{" Stmt "}"

  syntax Stmt   ::= Block
                  | Id "=" AExp ";" [strict(2)]
                  | "if" "(" BExp ")" Block "else" Block [strict(1)]
                  | "while" "(" BExp ")" Block [strict(1)]
                  > Stmt Stmt       [left]

  syntax Pgm    ::= "int" Ids ";" Stmt
endmodule

module IMP
  imports IMP-SYNTAX
  imports DOMAINS

  syntax KResult ::= Int | Bool

  configuration
    <T color="yellow">
      <k color="green"> $PGM:Pgm </k>
      <state color="red"> .Map </state>
    </T>
endmodule
