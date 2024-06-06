// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module MISSINGBAR

  syntax Foo ::= foo ()
                 bar ()

  rule foo () => bar ()

endmodule

