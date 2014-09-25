// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "builtins/builtins.k"

module K-TECHNIQUE
    // all basic K syntax is in the SDF grammar directly,
    // but also needs to be defined in K - except for
    // a few things added by compiler passes.
    // Unfortunately, FlattenModules explicitly ignores
    // includes of K-TECHNIQUE and some other core modules,
    // so we have to declare things like isSet in less obvious places

    syntax KItem
endmodule

module K-LISTK-EXTRAS
  imports K-TECHNIQUE
  imports K-EQUAL-HOOKS

  syntax Bool ::= K "inKList" KList [function]
  syntax Bool ::= K "#inKList" KList [function]
  rule K:K inKList L:KList => K #inKList L ==K true
  rule K #inKList (_,,K:K,,_) => true
  rule isKResult(_:KResult,,K:K,,KL:KList) => isKResult(K,,KL)
  rule isKResult(.KList) => true
endmodule

module K-RESULT
    imports K-TECHNIQUE
    imports BOOL-HOOKS

    syntax KItem ::= KResult
    syntax Bool ::= isKResult(KItem) [function,klabel(isKResult)]

    //op .KList : -> List{KResult} [ditto metadata "latex=(renameTo \\ensuremath{\\dotCt{List\\{K\\}}})"] .

endmodule

module K-WRAPPERS-LABELS
    imports K-TECHNIQUE

    //syntax KLabel ::= "KLabel2KLabel" KLabel
                    //| "CellLabel2KLabel" CellLabel
                    //| "KList2KLabel" KList
                    //| "Bag2KLabel" Bag
                    //| "Set2KLabel" Set
                    //| "List2KLabel" List
                    //| "Map2KLabel" Map
                    //| "wrap-with"



  //rule isSet(Set2KLabel(_)(.KList)) => true [predicate,anywhere]

endmodule

module K-DESTRUCTORS
  syntax KLabel ::= "getKLabel" K  [function, hook(MetaK:getKLabel_)]
  rule getKLabel(L:KLabel(_:KList)) => L

endmodule

module K-WRAPPERS
    imports K-TECHNIQUE
// not used anymore
//    syntax K ::= KLabel2K (KLabel)        [klabel('KLabel2K_)]
//               | Celllabel2K (CellLabel)[klabel('Celllabel2K_)]
//               | KList2K (KList)        [klabel('KList2K_)]
//               | Set2K (Set)            [klabel('Set2K_)]
//               | Bag2K (Bag)            [klabel('Bag2K_)]
//               | List2K (List)            [klabel('List2K_)]
//               | Map2K (Map)            [klabel('Map2K_)]
endmodule

module K-FREZERS
  imports K-TECHNIQUE
  syntax KLabel ::= "#freezer" K
  syntax KLabel ::= "heat" | "heated" | "redex" | "cool"

  rule heat(heated(K:K)) => K
  rule heat(heated(_,,K:K,,_)) => K
     [heat-choice]

  rule heat((redex(_:K,, K:K,, KL:KList) => K,,KL),,_)
    [owise]
  rule heat((redex(K:K) => .KList),,_,,heated(_,,(.KList => K)))
    [owise]

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

module K
  imports K-TECHNIQUE
  imports DEFAULT-CONFIGURATION
  imports K-WRAPPERS
  imports K-WRAPPERS-LABELS
  imports K-RESULT             // to express results syntactically
  // imports K-RULES              // to write k rules with in-place rewriting
  //imports K-EVAL
  // imports K-CONTEXTS
  imports K-DESTRUCTORS           // defines getKLabel and getKList for K
  //imports K-EXTRAS                // defines a KLabel substitution
  imports K-FREZERS
  imports K-LISTK-EXTRAS
  imports K-TOKENS
  //imports K-LATEX
endmodule

