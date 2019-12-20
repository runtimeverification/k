// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "a.k"

module A6-NOT-MATCH-IN-REQUIRES-SPEC
  imports A

  rule <k> foo(arg2(X)) => baz ... </k>

  rule <k> bar(Arg) => baz ... </k>
      requires arg1(_) :/=K  Arg
      [trusted]

endmodule
