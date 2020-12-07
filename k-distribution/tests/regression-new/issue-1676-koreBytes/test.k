// testing that krun pretty prints corectly Bytes
// kx should replace krun though, so if this test
// prevents a future upgrade, it should be removed

module TEST
    imports BYTES
    imports INT

    configuration <k> $PGM:Int </k>
    rule 1 => Int2Bytes(0, 0, LE)
endmodule
