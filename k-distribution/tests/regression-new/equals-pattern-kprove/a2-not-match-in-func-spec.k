// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "a.k"

module A2-NOT-MATCH-IN-FUNC-SPEC
  imports A

  rule <k> foo(arg2(X)) => baz ... </k>

  rule <k> bar(Arg) => baz ... </k>
      requires isNotArg1(Arg)
      [trusted]

endmodule
