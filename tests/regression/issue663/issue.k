// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/model-checker.k"

module ISSUE
  imports LTL-HOOKS
  imports MODEL-CHECKER-HOOKS

  configuration <k> $PGM:K </k><out stream="stdout"> .List </out>

  syntax A ::= "a" | "b"

  rule <k> a => b </k> <out>... .List => ListItem(5) </out> [transition]
endmodule
