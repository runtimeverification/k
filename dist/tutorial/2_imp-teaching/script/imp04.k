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
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule not(T:Bool) => notBool T
  rule true and B:BExp => B
  rule false and _ => false

  rule skip => .
  rule <k> X := I:Int => . ...</k>
       <state>... X |-> (_ => I) ...</state>
  rule S1 ; S2 => S1 ~> S2  [structural]
  rule if true then S else _ => S
  rule if false then _ else S => S
  rule while B do S
    => if B then (S ; while B do S) else skip  [structural]

  rule <k> var (X:Id,Xs:Ids => Xs); _ </k>
       <state> Rho:Map (. => X |-> 0) </state>
    when notBool(X in keys(Rho))
  rule <k> var .Ids; S => S </k>  [structural]

endmodule
