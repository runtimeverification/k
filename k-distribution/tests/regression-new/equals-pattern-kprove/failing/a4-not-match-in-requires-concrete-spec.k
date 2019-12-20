// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "a.k"

module A4-NOT-MATCH-IN-REQUIRES-SPEC
  imports A

  rule <k> foo(arg2(X)) => baz ... </k>

  rule <k> bar(Arg) => baz ... </k>
      requires arg2(_) :/=K  arg1(0)
      [trusted]

endmodule
