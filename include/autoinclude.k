// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "k-prelude.k"
require "builtins/symbolic-k.k"
require "io/uris.k"
require "builtins/map-impl.k"
require "builtins/set-impl.k"
require "builtins/list-impl.k"
require "builtins/mint-impl.k"
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
  imports LIST-IMPL
  imports MAP-IMPL
  imports SET-IMPL
  imports MINT-IMPL
  imports K-IO
  imports K-LISTK-EXTRAS
endmodule
