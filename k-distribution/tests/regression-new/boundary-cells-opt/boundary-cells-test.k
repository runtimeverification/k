// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "domains.k"

module BOUNDARY-CELLS-TEST

  imports DOMAINS

  configuration <T>
    <k> $PGM:K </k>
    <c1> 0 </c1>
    <c2> 0 </c2>
  </T>

  rule <k> I:Int => I +Int 1 ...</k>
       <c1> _ => (I +Int 1) /Int 2 </c1>
       <c2> _ => (I +Int 1) %Int 2 </c2>

endmodule
