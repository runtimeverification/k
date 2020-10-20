// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "a.k"

module A-SPEC

  imports A

  // #isVariable(X) == true
  claim <k> foo(X:Int) => bar(X) ... </k>

  // #isVariable(f(X)) == false
  claim <k> foo(f(X:Int)) => zoo(f(X)) ... </k>

  // #isVariable(3) == false
  claim <k> foo(3) => zoo(3) ... </k>

endmodule
