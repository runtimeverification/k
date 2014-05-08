// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module ISSUE
  syntax Exp ::= "`" Id
  syntax Id ::= "a"
  syntax K ::= "start"

  configuration <k> $PGM:K </k> <out stream="stdout"> .List </out>

  rule <k> start => ` a ...</k> <out>... .List => ListItem("ok") </out>
endmodule
