// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "a.k"

module A1-MATCH-IN-FUNC-SPEC
  imports A

  rule <k> foo(arg1(X)) => baz ... </k>

  rule <k> bar(Arg) => baz ... </k>
      requires isArg1(Arg)
      [trusted]

endmodule
