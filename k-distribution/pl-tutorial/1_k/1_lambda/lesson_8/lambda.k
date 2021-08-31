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

  syntax Exp  ::= "let" KVar "=" Exp "in" Exp
                | "mu" KVar "." Exp [binder]
                | "letrec" KVar KVar "=" Exp "in" Exp
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

  rule let V = E1 in E2 => (lambda V . E2) E1 [macro]

  rule letrec F X = E in E' =>
    let F = mu F . lambda X . E in E' [macro]

  rule mu X . E => E[(mu X . E) / X]

endmodule
