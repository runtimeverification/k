// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module EXITCODE-SYNTAX
    imports INT

    syntax Pgm ::= Int
endmodule

module EXITCODE
    imports EXITCODE-SYNTAX

    configuration
      <actualTop>
        <k> $PGM:Pgm </k>
        <exit-code exit=""> 0 </exit-code>
      </actualTop>

    rule <k> I:Int => .K ... </k>
         <exit-code> _ => I </exit-code>

endmodule
