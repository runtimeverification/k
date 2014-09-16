// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module ISSUE

  syntax Exp ::= Exp ":" Exp [hybrid]
               | Exp "," Exp [hybrid(1)]
               | Int | String
  syntax KResult ::= Int

  configuration <k> $PGM:Exp </k><out stream="stdout"> .List </out>

  rule <k> E:KResult => . </k>
       <out>... . => ListItem("foo") </out>

endmodule
