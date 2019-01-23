// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"
module TEST-SYNTAX
imports TEST
endmodule
module TEST
imports MAP
configuration <T>
  <k> $PGM:K </k>
  <x>
    <a> .K </a>
    <b> .K </b>
    <c> .K </c>
  </x>
</T>

syntax KItem ::= frag(XCellFragment)

rule frag(<x>-fragment <a> A </a> noBCell noCCell </x>-fragment) => .K
endmodule
