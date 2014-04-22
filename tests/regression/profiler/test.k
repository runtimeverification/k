// Copyright (c) 2012-2014 K Team. All Rights Reserved.

module TEST
     syntax K ::= "a" | "b"
     configuration <k> $PGM:K </k>
     rule a => b
endmodule
