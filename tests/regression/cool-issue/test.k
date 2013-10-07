module TEST
syntax K ::= "map" | "toMap"
configuration <k> $PGM:K </k>
rule map => toMap [supercool]
endmodule
