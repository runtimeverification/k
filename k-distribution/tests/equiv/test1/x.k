require "domains.k"

module X-SYNTAX
imports DOMAINS-SYNTAX
syntax PgmX ::= "runX"
endmodule

module CFG
imports X-SYNTAX
configuration
<L1>
  <k> $PGM:PgmX </k>
</L1>
endmodule

module X
imports DOMAINS
imports CFG
rule <k> runX => 2 ... </k>
endmodule
