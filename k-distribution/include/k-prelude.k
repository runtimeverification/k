// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "builtins/builtins.k"

module K-TECHNIQUE
    // all basic K syntax is in the SDF grammar directly,
    // but also needs to be defined in K - except for
    // a few things added by compiler passes.
    // Unfortunately, FlattenModules explicitly ignores
    // includes of K-TECHNIQUE and some other core modules,
    // so we have to declare things like isSet in less obvious places

    syntax KItem
    syntax K
    syntax KList
    syntax KLabel
    syntax Bag
    syntax BagItem
    syntax KList ::= K
    syntax K ::= KItem
endmodule

module K-LISTK-EXTRAS
  imports K-TECHNIQUE
  imports K-EQUAL-HOOKS

  syntax Bool ::= K "inKList" KList [function]
  syntax Bool ::= K "#inKList" KList [function]
  rule K:K inKList L:KList => K #inKList L ==K true
  rule K #inKList (_,,K:K,,_) => true
  rule isKResult(.KList) => true
endmodule

module K-RESULT
    imports K-TECHNIQUE
    imports BOOL-HOOKS

    syntax KResult
    syntax KItem ::= KResult
    syntax Bool ::= isKResult(KItem) [function,klabel(isKResult)]

endmodule

module K-DESTRUCTORS
  imports K-TECHNIQUE
  syntax KLabel ::= "getKLabel" K  [function, hook(KREFLECTION.getKLabel), impure]
  rule getKLabel(L:KLabel(_:KList)) => L

endmodule

module K-FREEZERS
  imports K-TECHNIQUE
  syntax KLabel ::= "#freezer" K

  syntax K ::= cool(K) [function, klabel(cool)]

  rule cool(K:K) => K [owise]
endmodule

module DEFAULT-CONFIGURATION
  imports K-TECHNIQUE
  configuration <k> $PGM:K </k>
endmodule

module K-TOKENS
  imports K-TECHNIQUE
  syntax KLabel ::= "#token"
  syntax Bool ::= isToken(K) [predicate, hook(#PREDICATE:isToken)]
  rule isToken(#token(_)) => true
  syntax Bool ::= isBuiltin(K)
  //[klabel(isBuiltin), predicate, hook(#PREDICATE:isBuiltin)]
  [prefixlabel(isBuiltin), klabel(isBuiltin), predicate, hook(#PREDICATE:isBuiltin)]
endmodule

module K-REFLECTION
  imports K-TECHNIQUE

  syntax Bag ::= "#configuration" [function, impure, hook(KREFLECTION.configuration)]

endmodule

module K
  imports K-TECHNIQUE
  imports DEFAULT-CONFIGURATION
  imports K-RESULT             // to express results syntactically
  imports K-DESTRUCTORS           // defines getKLabel and getKList for K
  imports K-FREEZERS
  imports K-LISTK-EXTRAS
  imports K-TOKENS
  imports K-REFLECTION
endmodule

