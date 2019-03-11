// Copyright (c) 2019 K Team. All Rights Reserved.

module SYMBINT-SYNTAX
  imports INT

  syntax Int ::= "symbolicIntMemo"   [function, memo]
               | "symbolicIntNoMemo" [function]
  rule symbolicIntMemo   => ?V:Int
  rule symbolicIntNoMemo => ?V:Int

  syntax Int ::= init ( Int ) | final ( Int , Int )
endmodule

module SYMBINT
  imports SYMBINT-SYNTAX

  configuration <k> $PGM:Int </k>

  rule <k> init(0) => final(symbolicIntMemo, symbolicIntMemo) </k>
  rule <k> init(1) => final(symbolicIntNoMemo, symbolicIntNoMemo) </k>
endmodule
