// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "domains.k"

module A

  imports DOMAINS

  configuration <T>
    <k> $PGM:Term </k>
    <c1> .K </c1>
    <c2> .K </c2>
    <c3> .K </c3>
  </T>

  syntax Term ::= "a" | "b" | "d"

  syntax Term ::= #f1 ( Term ) [function]
                | #f2 ( Term ) [function]
                | #f3 ( Term ) [function]
                | #g ( Term )

  rule a => b

endmodule
