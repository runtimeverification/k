// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// error if a config variable is not initialized in command line
// warning if a variable is specified but not declared in the configuration

module TEST
    imports INT
    configuration <k> $PGM:Int </k>
                  <foo> $Foo:Int </foo>
endmodule
