// Copyright (c) K Team. All Rights Reserved.
module TEST-SYNTAX
  imports INT-SYNTAX

  syntax Int ::=
      "(" Int ")" [bracket]
    | "-" Int     [function, group(unmin)]
    | Int "*" Int [function, group(muldiv)]
    | Int "/" Int [function, group(muldiv)]
    | Int "+" Int [function, group(plusmin,lefty)]
    | Int "-" Int [function, group(plusmin,lefty)]

  syntax priority unmin > muldiv > plusmin
  syntax left lefty
  syntax left muldiv
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT

  rule    - I2 => 0    -Int I2
  rule I1 * I2 => I1   *Int I2
  rule I1 / I2 => I1 divInt I2
  rule I1 + I2 => I1   +Int I2
  rule I1 - I2 => I1   -Int I2
endmodule
