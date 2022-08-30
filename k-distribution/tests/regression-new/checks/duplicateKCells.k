module DUPLICATEKCELLS-SYNTAX

    configuration <k> $PGM:K </k>

endmodule

module DUPLICATEKCELLS
    imports DUPLICATEKCELLS-SYNTAX

    configuration <k> $PGM:Int </k>

    configuration <k>
                      <k> $PGM:Int </k>
                      <state> .Map </state>
                  </k>

endmodule
