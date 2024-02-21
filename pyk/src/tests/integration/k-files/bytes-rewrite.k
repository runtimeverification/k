module BYTES-REWRITE-SYNTAX
    imports BYTES-SYNTAX
endmodule

module BYTES-REWRITE
    imports BYTES-REWRITE-SYNTAX
    imports BYTES

    configuration <k> $PGM:Bytes </k>
                  <b> b"" </b>

    rule <k> B => .K ... </k>
         <b> _ => B      </b>
endmodule
