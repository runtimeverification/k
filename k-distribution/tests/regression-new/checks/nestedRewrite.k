// Copyright (c) K Team. All Rights Reserved.
module NESTEDREWRITE
  imports INT

rule (1 => 2) => 3
rule 1 => (2 => 3)
rule 1 => 2

endmodule
