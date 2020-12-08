// Copyright (c) 2019 K Team. All Rights Reserved.

module SYMBINT-SYNTAX
  imports INT

  syntax Int ::= "symbolicIntMemo"   [function, memo]
               | "symbolicIntNoMemo" [function]
               | "symbolicIntImpure" [function, impure]
  rule symbolicIntMemo   => ?V:Int
  rule symbolicIntNoMemo => ?V:Int
  rule symbolicIntImpure => ?V:Int

  syntax Exp ::= init ( Int ) | final ( Int , Int )
endmodule

module SYMBINT
  imports SYMBINT-SYNTAX

  configuration <k> $PGM:Exp </k>

  rule <k> init(0) => final(symbolicIntMemo, symbolicIntMemo)     </k>
  rule <k> init(1) => final(symbolicIntNoMemo, symbolicIntNoMemo) </k>
  rule <k> init(2) => final(symbolicIntImpure, symbolicIntImpure) </k>
endmodule
