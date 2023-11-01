// Copyright (c) K Team. All Rights Reserved.
module TEST
  imports K-REFLECTION
  imports INT
  configuration <k> #parseKORE("\\dv{SortInt{}}(\"1\")"):Int </k>

  rule 1 => 2
endmodule
