require "k-prelude.k"
require "builtins/symbolic-k.k"
require "io/uris.k"
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

endmodule
