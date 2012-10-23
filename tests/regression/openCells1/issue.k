module ISSUE
  configuration <T>
                  <k> $PGM:K </k>
                  <out stream="stdout"> .List </out>
		</T>
  syntax K ::= "test1" | "test2" | K ";" K [left]

  rule K1 ; K2 => K1 ~> K2 [macro]

  rule <k> test1 => . ...</k>
       <out>... . => ListItem(1) </out>

  rule test2 => . 
endmodule
