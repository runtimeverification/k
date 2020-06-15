module TEST
  imports DOMAINS
  imports K-REFLECTION

  syntax Exp ::= abc(Int) [klabel(abc), symbol]

  configuration <k> $PGM:K </k> <state> #parseKORE("Lblabc{}(\\dv{SortInt{}}(\"1\"))"):Exp </state>

  rule <k> 0 => 1 </k> <state> abc(1) </state>

endmodule
