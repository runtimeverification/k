// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module ISSUE
  configuration <T>
                  <k> $PGM:K </k>
                  <out stream="stdout"> .List </out>
        </T>
  syntax KItem ::= "test1" | "test2" | K ";" K [left]

  rule K1 ; K2 => K1 ~> K2 [macro]

  rule <k> test1 => . ...</k>
       <out>... .List => ListItem(1) </out>

  rule test2 => .
endmodule
