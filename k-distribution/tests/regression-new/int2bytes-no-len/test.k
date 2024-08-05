// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// testing that krun pretty prints corectly Bytes
// kx should replace krun though, so if this test
// prevents a future upgrade, it should be removed

module TEST
    imports BYTES
    imports INT

    configuration <k> $PGM:Int </k>
    rule 0 => Int2Bytes(0, LE, Unsigned) +Bytes Int2Bytes(0, LE, Signed)
    rule 1 => Int2Bytes(1025, LE, Unsigned)
    rule 2 => Int2Bytes(1025, LE, Signed)
    rule 3 => Int2Bytes(-1, LE, Signed)
    rule 4 => Int2Bytes(-1025, LE, Signed)

    rule 10 => Int2Bytes(0, BE, Unsigned) +Bytes Int2Bytes(0, BE, Signed)
    rule 11 => Int2Bytes(1025, BE, Unsigned)
    rule 12 => Int2Bytes(1025, BE, Signed)
    rule 13 => Int2Bytes(-1, BE, Signed)
    rule 14 => Int2Bytes(-1025, BE, Signed)

endmodule
