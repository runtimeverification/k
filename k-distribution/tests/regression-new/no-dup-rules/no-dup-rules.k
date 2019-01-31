// Copyright (c) 2019 K Team. All Rights Reserved.

module NO-DUP-RULES-INIT
    imports STRING-BUFFER
    imports MAP
    imports COLLECTIONS

    syntax KResult ::= Int

    syntax Int ::= #parseHexWord ( String ) [function]
                 | #parseWord    ( String ) [function]
 // --------------------------------------------------
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16) requires (S =/=String "") andBool (S =/=String "0x")

    rule #parseWord("") => 0
    rule #parseWord(S)  => #parseHexWord(S) requires lengthString(S) >=Int 2 andBool substrString(S, 0, 2) ==String "0x"
    rule #parseWord(S)  => String2Int(S) [owise]
endmodule

module NO-DUP-RULES-SYNTAX
    imports STRING
    imports NO-DUP-RULES-INIT

    configuration
      <k> $PGM:Int </k>

    syntax Exp ::= Ccall ( BExp ) [strict]
 // --------------------------------------

    syntax BExp ::= Bool
endmodule

module NO-DUP-RULES
    imports NO-DUP-RULES-SYNTAX
    imports K-REFLECTION
endmodule
