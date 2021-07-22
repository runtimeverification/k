// Copyright (c) 2016-2021 K Team. All Rights Reserved.

module CHECKCELLSORTDECLOKISSUE-SYNTAX
endmodule

module EVM
    imports INT

    configuration
      <kevm>
        <k> $PGM:Int </k>
        <account> 0 </account>
      </kevm>

endmodule

module CHECKCELLSORTDECLOKISSUE
    imports EVM

    configuration
      <kevm-client>
        <kevm/>
        <foo> $FOO:KItem </foo>
      </kevm-client>

    syntax AccountItem ::= AccountCell
 // ----------------------------------

endmodule
