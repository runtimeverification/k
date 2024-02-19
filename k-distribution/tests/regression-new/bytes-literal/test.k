// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
    imports BYTES
    imports BOOL
    imports K-EQUAL

    syntax Bool ::= bytesEq(Bytes, Bytes) [function]
    configuration <k> $PGM:Bool </k>

    rule bytesEq(B1, B2) => true requires B1 ==K B2
    rule bytesEq(_B1, _B2) => false [owise]
endmodule
