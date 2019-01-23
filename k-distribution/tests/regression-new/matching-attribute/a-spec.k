// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "a.k"

module A-SPEC

  imports A

  rule <k> a => d ... </k>
       <c1> #f1(a) => #g(a) </c1>
       <c2> #f2(a) => #g(a) </c2>
       <c3> #f1(#f3(a)) => #g(a) </c3>

  rule <k> b => d ... </k>
       <c1> #f1(X) => #g(X) </c1>
       <c2> #f2(Y) => #g(Y) </c2>
       <c3> #f1(#f3(Z)) => #g(Z) </c3>
       [trusted, matching(#f1,#f2,#f3)]

endmodule
