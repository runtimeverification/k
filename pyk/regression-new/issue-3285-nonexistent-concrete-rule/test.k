// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
imports INT-SYNTAX
syntax Exp ::= Int
             | Exp "+" Exp
             | Exp "*" Exp
endmodule

module TEST
imports TEST-SYNTAX
imports INT

rule [assoc]: (X + Y) + Z => X + (Y + Z)
rule [distrib]: X * (Y + Z) => (X * Y) + (X * Z)

endmodule