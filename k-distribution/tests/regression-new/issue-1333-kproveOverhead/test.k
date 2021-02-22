// Copyright (c) 2020 K Team. All Rights Reserved.
module TEST
    imports DOMAINS

    configuration
        <k> $PGM:Int </k>

    syntax Int ::= inc ( Int ) [function]
    rule inc(I) => I +Int 1
endmodule

module TEST-CLAIMS
    imports TEST
    claim <k> inc(3) => I </k>
      requires I ==Int 4
endmodule