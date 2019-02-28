module NESTEDFUNCTIONCONTEXTINFUN
  imports INT
  imports MAP
  imports BOOL

configuration <k> $PGM:K </k> <bar> 0 </bar>

rule 0 => #fun([[0 => 1]] <bar> 0 </bar>)(0)

rule 0 => #fun([[[[0 => 1]] <bar> 0 </bar>]] <bar> 0 </bar>)(0)

endmodule
