// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module TEST
syntax K ::= "map" | "toMap"
configuration <k> $PGM:K </k>
rule map => toMap [supercool]
endmodule
