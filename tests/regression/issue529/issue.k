// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module ISSUE

syntax Fo ::= bar(KLabel)

rule bar(List2KLabel _) => .
rule bar(KList2KLabel _) => .

endmodule
