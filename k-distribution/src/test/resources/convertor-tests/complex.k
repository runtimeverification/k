// Copyright (c) K Team. All Rights Reserved.

module TEST
  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
  syntax Bool ::= #Bool

  rule true => .KList
  rule true => true ,, .KList
endmodule
