// Copyright (c) 2012-2018 K Team. All Rights Reserved.
require "domains.k"
module UNIFICATION
  imports SET

  syntax K ::= #renameVariables(K)  [function, hook(UNIFICATION.renameVariables), impure]

  syntax Set ::= #variables(K)    [function, hook(UNIFICATION.variables), impure]

  syntax Set ::= #metaKVariables(K)    [function, hook(UNIFICATION.metaVariables), impure]

  syntax KItem ::= #variablesMap(K) [function, hook(UNIFICATION.variablesMap), impure]

  syntax K ::= #renameMetaKVariables(K, Set)    [function, hook(UNIFICATION.rename), impure, poly(0, 1)]

  syntax K ::= #freezeKVariables(K, K) [function, hook(UNIFICATION.freezeVariables), impure, poly(0, 1)]

  syntax Bool ::= #unifiable(K,K) [function, hook(UNIFICATION.unifiable), impure]

  syntax K ::= #unify(K, K) [function, hook(UNIFICATION.unify), impure]

  syntax MetaVariable

endmodule
