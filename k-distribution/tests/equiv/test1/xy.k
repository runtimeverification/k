require "domains.k"

// require "./x.k"
module X-SYNTAX
imports DOMAINS-SYNTAX
syntax PgmX ::= "runX"
endmodule
// require "./y.k"
module Y-SYNTAX
imports DOMAINS-SYNTAX
syntax PgmY ::= "runY"
endmodule

module XY-SYNTAX
imports X-SYNTAX
imports Y-SYNTAX
endmodule

module CFG
imports XY-SYNTAX
configuration
<T>
<L1>
  <k> $PGM:PgmX </k>
</L1>
<L2>
  <k> $PGM:PgmY </k>
</L2>
</T>
endmodule

module XY
imports DOMAINS
imports CFG
endmodule
