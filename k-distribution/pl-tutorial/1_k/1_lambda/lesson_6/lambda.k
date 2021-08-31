requires "substitution.md"

module LAMBDA-SYNTAX
  imports KVAR-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Val  ::= KVar
                | "lambda" KVar "." Exp [binder]

  syntax Val  ::= Int | Bool

  syntax Exp  ::= Val
                | Exp Exp [left, strict]
                | "(" Exp ")" [bracket]

  syntax Exp  ::= Exp "*"  Exp [strict, left]
                | Exp "/"  Exp [strict, left]
                > Exp "+"  Exp [strict, left]
                | Exp "-"  Exp [strict, left]
                > Exp "<=" Exp [strict]

  syntax Exp  ::= "if" Exp "then" Exp "else" Exp [strict(1)]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION
  imports INT
  imports BOOL

  syntax KResult ::= Val

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]

  rule I1:Int *  I2:Int => I1  *Int I2
  rule I1:Int /  I2:Int => I1  /Int I2
  rule I1:Int +  I2:Int => I1  +Int I2
  rule I1:Int -  I2:Int => I1  -Int I2

  rule I1:Int <= I2:Int => I1 <=Int I2

  rule if true  then E else _ => E
  rule if false then _ else E => E
endmodule
