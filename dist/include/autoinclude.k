require "k-prelude.k"
require "builtins/symbolic-k.k"
require "io/uris.k"
// require "builtins/smt.k"
// require "modules/substitution.k"

interface AUTO-INCLUDED-MODULE-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

endinterface

interface AUTO-INCLUDED-MODULE
  imports BUILTIN-HOOKS
  imports K
  imports SYMBOLIC-K
  imports URIS

endinterface
