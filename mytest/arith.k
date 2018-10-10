// Copyright (c) 2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
module ARITH-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int
                 | "-" AExp                   [strict]
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax Pgm ::= AExp
endmodule


module ARITH
  imports ARITH-SYNTAX
  imports DOMAINS
  syntax KResult ::= Int

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                </T>

// AExp
  syntax Bool ::= isBeautiful(Int) [function]
  syntax Bool ::= isPretty(Int)    [function]
  syntax Bool ::= isNice(Int)      [function]

  rule isBeautiful(I::Int) => I =/=Int 2 requires isPretty(I)
  rule isPretty(I::Int) => I =/=Int 1 requires isNice(I)
  rule isNice(I::Int) => true requires I >Int 0

  // Normal rule
  rule I1 + I2 => I1 +Int I2

  // A rule with function call in side condition
  rule I1 / I2 => I1 /Int I2  requires isBeautiful(I2)

  // A rule with nested function call
  rule - I1 => #if isBeautiful(I1) #then 0 -Int I1 #else I1 #fi

endmodule
