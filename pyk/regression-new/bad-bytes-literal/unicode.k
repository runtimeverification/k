// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module UNICODE
    imports BYTES
    configuration <k> $PGM:Bool </k>

    rule <k> b"\x😃" => b"" </k>
endmodule
