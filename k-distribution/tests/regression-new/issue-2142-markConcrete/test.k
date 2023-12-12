// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module SERIALIZATION
    imports INT
    imports BYTES

    syntax Int ::= keccak ( Bytes ) [function, total, smtlib(smt_keccak)]
 // --------------------------------------------------------------------------
    rule [keccak]: keccak(_) => 1

endmodule

module TEST
    imports SERIALIZATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Int
 // -------------------

endmodule
