// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
    imports DOMAINS

    configuration
        <k> $PGM:Int </k>

    syntax Int ::= inc ( Int ) [function]
    rule inc(I) => I +Int 1
endmodule
