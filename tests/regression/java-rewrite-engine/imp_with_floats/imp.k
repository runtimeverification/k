require "builtins/map.k"

module IMP-SYNTAX
  syntax AExp  ::= Float | Id
                 | AExp "/" AExp              [left, seqstrict]
                 > AExp "+" AExp              [left, seqstrict]
                 | AExp "-" AExp              [left, seqstrict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp ">" AExp              [seqstrict]
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | Id "=" AExp ";"            [strict(2)]
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "float" Ids ";" Stmt
  syntax Ids ::= List{Id,","}

  // special identifiers (for matching-logic specifications)
  syntax Id ::= Token{"n"} | Token{"sum"}   [prefer]
endmodule

module IMP
  imports IMP-SYNTAX
  imports MAP
  syntax KResult ::= Float | Bool

  configuration <T color="yellow">
                  //<k color="green"> $PGM:Pgm </k>
                  <k color="green"> $PGM:K </k>
                  <state color="red"> .MyMap </state>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I:KItem ...</state>
  rule I1:Float / I2:Float => I1 /Float I2
  rule I1:Float + I2:Float => I1 +Float I2
  rule I1:Float - I2:Float => I1 -Float I2
// BExp
  rule I1:Float > I2:Float => I1 >Float I2
  rule I1:Float <= I2:Float => I1 <=Float I2
  rule ! T:Bool => notBool T
  rule true && B:KItem => B
  rule false && _:KItem => false
// Block
  rule {} => .   [structural]
  rule {S:KItem} => S  [structural]
// Stmt
  rule <k> X:Id = I:Float; => . ...</k>
       <state>... X |-> (_:KItem => I) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S:KItem else _:KItem => S
  rule if (false) _:KItem else S:KItem => S
  rule while (B:KItem) S:KItem => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule
    <k> float (X:Id,Xs:Ids => Xs); _:KItem </k>
    <state> Rho:MyMap (.MyMap => X |-> 0.0) </state>
    //when notBool (X in keys(Rho))
  rule float .Ids; S:KItem => S  [structural]
endmodule
