// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "domains.k"
module UNIFICATION
  imports SET

  syntax K ::= #renameVariables(K)  [function, hook(UNIFICATION.renameVariables), impure]

  syntax Set ::= #variables(K)    [function, hook(UNIFICATION.variables), impure]

  syntax Set ::= #metaVariables(K)    [function, hook(UNIFICATION.metaVariables), impure]

  syntax KItem ::= #variablesMap(K) [function, hook(UNIFICATION.variablesMap), impure]

  syntax K ::= #rename(K, Set)    [function, hook(UNIFICATION.rename), impure]

  syntax K ::= #freezeVariables(K, K) [function, hook(UNIFICATION.freezeVariables), impure]

  syntax Bool ::= #unifiable(K,K) [function, hook(UNIFICATION.unifiable), impure]

  syntax MetaVariable

endmodule
