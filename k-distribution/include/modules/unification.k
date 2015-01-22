// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "builtins/set.k"
module UNIFICATION
  imports SET

  syntax K ::= #renameVariables(K)  [function, hook(MetaK:renameVariables), impure]

  syntax Set ::= #variables(K)    [function, hook(MetaK:variables), impure]

  syntax Set ::= #metaVariables(K)    [function, hook(#META-K:#variables), impure]

  syntax KItem ::= #variablesMap(K) [function, hook(MetaK:variablesMap), impure]

  syntax K ::= #rename(K, Set)    [function, hook(#META-K:#rename), impure]

  syntax K ::= #freezeVariables(K, K) [function, hook(MetaK:freezeVariables), impure]

  syntax Bool ::= #unifiable(K,K) [function, hook(MetaK:unifiable), impure]

  syntax MetaVariable

endmodule
