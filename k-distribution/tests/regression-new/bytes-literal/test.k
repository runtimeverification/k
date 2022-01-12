module TEST
    imports BYTES

    configuration <k> $PGM:Bytes </k>

    rule <k> b"\x80\x00\x80" => b"\x80\x00" ... </k>
endmodule
