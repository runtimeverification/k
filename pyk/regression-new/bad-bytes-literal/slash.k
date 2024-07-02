// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module SLASH
    imports BYTES
    configuration <k> $PGM:Bool </k>

    rule <k> b"\" => b"" </k>
endmodule
