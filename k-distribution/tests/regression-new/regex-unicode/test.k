// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
syntax lexical Emote = r"😊?[😦🙁]+"

syntax Emoji ::= r"{Emote}" [token]

endmodule

module TEST
imports TEST-SYNTAX
configuration <k> $PGM:Emoji </k>
rule <k>😊🙁 => 😊😦😦</k>
endmodule
