require "domains.k"

module Y-SYNTAX
imports DOMAINS-SYNTAX
syntax PgmY ::= "runY"
endmodule

module CFG
imports Y-SYNTAX
configuration
<L2>
  <k> $PGM:PgmY </k>
</L2>
endmodule

module Y
imports DOMAINS
imports CFG
syntax KItem ::= "stepY"
rule runY => stepY
rule stepY => 2
endmodule
