// Copyright (c) K Team. All Rights Reserved.
module UNICODE
    imports BYTES
    configuration <k> $PGM:Bool </k>

    rule <k> b"\x😃" => b"" </k>
endmodule
