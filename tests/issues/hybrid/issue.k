module ISSUE

  syntax Exp ::= Exp ":" Exp [hybrid]
               | Int
  syntax KResult ::= Int

  configuration <k> $PGM:Exp </k><out stream="stdout"> .List </out>

  rule <k> E:KResult => . </k>
       <out>... . => ListItem("foo") </out>

endmodule
