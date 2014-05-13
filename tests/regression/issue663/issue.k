// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/model-checker.k"

module ISSUE
  imports LTL-HOOKS
  imports MODEL-CHECKER-HOOKS

  syntax A ::= "a" | "b"

  rule a => b [transition]
endmodule
