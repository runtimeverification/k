// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "k-prelude.k"
require "builtins/symbolic-k.k"
require "io/uris.k"
require "builtins/map.k"
require "builtins/set.k"
require "builtins/list.k"
require "io/io.k"
// require "builtins/smt.k"
// require "modules/substitution.k"

module AUTO-INCLUDED-MODULE-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS
  
endmodule

module AUTO-INCLUDED-MODULE
  imports BUILTIN-HOOKS
  imports K
  imports SYMBOLIC-K
  imports URIS
  imports LIST
  imports MAP
  imports SET
  imports IO

endmodule
