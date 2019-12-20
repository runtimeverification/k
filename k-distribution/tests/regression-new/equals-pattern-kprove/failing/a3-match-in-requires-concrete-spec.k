// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "a.k"

module A3-MATCH-IN-REQUIRES-SPEC
  imports A

  rule <k> foo(arg1(X)) => baz ... </k>

  rule <k> bar(Arg) => baz ... </k>
      requires arg1(_) :=K  arg1(0)
      [trusted]

endmodule
