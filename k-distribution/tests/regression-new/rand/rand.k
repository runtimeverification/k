// Copyright (c) 2020 K Team. All Rights Reserved.

module RAND-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Pgm ::= ".Pgm" | Int ";" Pgm | seedRand ( Int ) | runRand ( )
endmodule


module RAND
  imports RAND-SYNTAX
  imports DOMAINS

  configuration <k> $PGM:Pgm </k>
                <rands> .List </rands>

  rule <k> I ; P => srandInt(I) ~> runRand() ~> P ... </k>

  rule <k> runRand() => . ... </k>
       <rands> ... .List => ListItem(randInt(1000)) </rands>
endmodule
