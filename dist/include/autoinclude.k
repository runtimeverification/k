require "k-prelude.k"
require "modules/uris.k"
// require "builtins/smt.k"
// require "modules/substitution.k"

interface AUTO-INCLUDED-MODULE-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

endinterface

interface AUTO-INCLUDED-MODULE
  imports BUILTIN-SYNTAX
  imports K
  imports URIS

endinterface
