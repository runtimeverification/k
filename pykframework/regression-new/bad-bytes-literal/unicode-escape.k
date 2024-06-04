// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module UNICODE-ESCAPE
    imports BYTES
    configuration <k> $PGM:Bool </k>

    rule <k> b"\u0012" => b"" </k>
endmodule
