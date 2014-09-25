// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/**
Test for issue 627.
Tagging a subsort should not automatically create a klabel for it.
*/

module ISSUE

syntax NAME ::= Id
syntax Exp ::= NAME [atom]
                      | tuple(Exp) [atom, klabel('Tuple)]
                      | Exp "." NAME [primary]

syntax priorities atom > primary

configuration <k> $PGM:K </k>
              <out stream="stdout"> .List </out>

syntax Id ::= "x"
rule 5 => isExp(x)
rule <k> true => . </k>
     <out>... .List => ListItem("Correct") </out>
endmodule
