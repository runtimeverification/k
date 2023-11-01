// Copyright (c) K Team. All Rights Reserved.
module SLASH
    imports BYTES
    configuration <k> $PGM:Bool </k>

    rule <k> b"\" => b"" </k>
endmodule
