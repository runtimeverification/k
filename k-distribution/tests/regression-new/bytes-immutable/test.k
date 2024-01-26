// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
    imports BYTES
    imports INT-SYNTAX

    configuration
      <test>
        <k> $PGM </k>
        <mem> .Bytes </mem>
        <stuff> .Bytes </stuff>
      </test>

    syntax KItem ::= "a" | "b" | "c" | "d"

    rule <k> a => b </k>
        <mem> _ => b"alice" </mem>
    rule <k> b => c </k>
        <mem> B </mem>
        <stuff> _ => B </stuff>
    rule <k> c => d </k>
        <mem> B => replaceAtBytes(B, 0:Int, b"bob__") </mem>
endmodule
