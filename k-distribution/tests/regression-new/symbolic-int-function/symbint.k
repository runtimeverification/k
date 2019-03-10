// Copyright (c) 2019 K Team. All Rights Reserved.

module SYMBINT-SYNTAX
  imports INT

  syntax Int ::= "symbolicInt" [function]
  rule symbolicInt => ?V:Int

  syntax Int ::= "init" | final ( Int , Int )
endmodule

module SYMBINT
  imports SYMBINT-SYNTAX

  configuration <k> $PGM:Int </k>

  rule <k> init => final(symbolicInt, symbolicInt) </k>
endmodule
