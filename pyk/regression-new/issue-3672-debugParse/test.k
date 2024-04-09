// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module TEST-SYNTAX
  imports UNSIGNED-INT-SYNTAX
  imports ID-SYNTAX

  syntax Exp ::= Int
               | "-" Exp      [group(neg)]
               | Exp "+" Exp  [left, group(add)]
               | Exp "-" Exp  [left, group(sub)]
               | Exp "*" Exp  [left, group(mul)]
               | Exp "/" Exp  [left, group(div)]
               | "(" Exp ")"  [bracket]

  syntax priority neg > mul div > add sub
endmodule

module TEST
  imports TEST-SYNTAX
  configuration <k> $PGM:Exp </k>
endmodule
