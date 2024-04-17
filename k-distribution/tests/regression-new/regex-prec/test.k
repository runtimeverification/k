// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
    syntax Exp ::= r"1"   [token, prec(-1)]
                 | r"0?1" [token]
		 | "foo"  [token]
endmodule

module TEST
    imports TEST-SYNTAX
    configuration <k> $PGM:Exp </k>
endmodule
