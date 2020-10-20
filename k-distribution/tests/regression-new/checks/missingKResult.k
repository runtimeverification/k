require "substitution.md"

module MISSINGKRESULT
  imports DOMAINS
  imports SUBSTITUTION

  syntax Exp ::= Val
               | Exp Exp
               | "(" Exp ")"          [bracket]

  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp
               | Exp "/" Exp          [strict]
               > Exp "+" Exp
               > Exp "<=" Exp
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2
endmodule
