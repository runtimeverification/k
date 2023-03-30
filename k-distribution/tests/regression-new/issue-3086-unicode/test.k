// Copyright (c) K Team. All Rights Reserved.
module TEST-SYNTAX
    syntax Emoji ::= r"🙁|🙂" [token]
endmodule

module TEST
    imports TEST-SYNTAX
    rule <k> 🙁 => 🙂 ... </k>
endmodule