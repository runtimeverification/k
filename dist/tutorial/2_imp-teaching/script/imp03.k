module IMP-SYNTAX

  syntax AExp ::= Int | Id
                | AExp "/" AExp    [left, strict]
                > AExp "+" AExp    [left, strict]
                | "(" AExp ")"     [bracket]
  syntax BExp ::= Bool
                | AExp "<=" AExp   [seqstrict, latex({#1}\leq{#2})]
                | "not" BExp       [strict]
                > BExp "and" BExp  [left, strict(1)]
                | "(" BExp ")"     [bracket]
  syntax Stmt ::= "skip"
                | Id ":=" AExp     [strict(2)]
                | "if" BExp
                  "then" Stmt
                  "else" Stmt      [strict(1)]
                | "while" BExp
                  "do" Stmt
                > Stmt ";" Stmt    [left]
                | "(" Stmt ")"     [bracket]

  syntax Pgm ::= "var" Ids ";" Stmt
  syntax Ids ::= List{Id,","}

endmodule


module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool
  
  configuration <T color="yellow">
                  <k color="green"> $PGM:K </k>
                  <state color="red"> .Map </state>
                </T>

  rule <k> X:Id => I ...</k>
       <state>... X |-> I ...</state>
endmodule
