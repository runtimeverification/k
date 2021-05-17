module MAPIMPORTINCONFIGMODULES-SYNTAX
  imports INT-SYNTAX
endmodule

module CONFIG
  imports INT
  syntax E ::= "balance"
  configuration <k> $PGM:Int </k> <balance> .Map </balance>

endmodule

module MAPIMPORTINCONFIGMODULES
  imports MAPIMPORTINCONFIGMODULES-SYNTAX
  imports INT
  imports CONFIG

  rule <balance> .Map => .Map </balance>
  rule <k> 0 => 1 </k>
endmodule
