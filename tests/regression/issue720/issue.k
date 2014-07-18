// Copyright (c) 2014 K Team. All Rights Reserved.
module ISSUE
  configuration <k> $PGM:K </k> <out stream="stdout"> .List </out>
  rule <k> X:Id => .K </k>
       <out>... .List => ListItem("Hello ") ListItem(Id2String(X)) </out>
       [hello]
  rule <k> X:Id => .K </k>
       <out>... .List => ListItem("Bye ") ListItem(Id2String(X)) </out>
       [bye]
endmodule
