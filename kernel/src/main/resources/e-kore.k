// Copyright (c) 2014 K Team. All Rights Reserved.

// Module defining only the sorts K and KString, useful for modularity
module BASIC-K
  syntax K
  syntax KString ::= r"[\\\"]([^\\\"\\n\\r\\\\]|[\\\\][nrtf\\\"\\\\])*[\\\"]"
                         [token, hook(org.kframework.kore.KString)]
    // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
  syntax KLabel
endmodule


module KAST
  imports BASIC-K
  syntax K     ::= KItem
  syntax KItem ::= "#token" "(" KString "," KString ")"
                       [klabel(#KToken), hook(org.kframework.kore.KToken)]
                 | "#klabel" "(" KLabel ")"
                       [klabel(#WrappedKLabel), hook(org.kframework.kore.meta.WrappedKLabel)]
                 | KLabel "(" KList ")" [klabel(#KApply), hook(org.kframework.kore.KApply)]

  syntax KLabel ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\s])+`" [klabel(#KLabel), token]
                  | r"[#a-z][a-zA-Z0-9]*"
                       [klabel(#KLabel), token, hook(org.kframework.kore.KLabel)]
                       // something that doesn't collide with meta-variables

  syntax KList ::= K
                 | ".::KList" [klabel(#EmptyKList), hook(org.kframework.kore.EmptyKList)]
                 | KList "," KList
                       [klabel(#KList), left, assoc, unit(#EmptyKList), hook(org.kframework.kore.KList)]
endmodule


// To be used when parsing/pretty-printing ground configurations
module KSEQ
  imports KAST
  syntax K     ::= ".::K" [klabel(#EmptyK), hook(org.kframework.kore.EmptyK)]
                  | K "~>" K
                       [klabel(#KSequence), left, assoc, unit(#EmptyK), hook(org.kframework.kore.KSequence)]
endmodule


// To be used when parsing/pretty-printing symbolic configurations
module KSEQ-SYMBOLIC
  imports KSEQ
  syntax KVariable ::= r"(?<![A-Za-z0-9\\_])(\\$|\\!|\\?)?([A-Z][A-Za-z0-9']*|_)"
                           [hook(org.kframework.kore.KVariable)]
  syntax KItem     ::= KVariable
  syntax KLabel    ::= KVariable
endmodule



// To be used to parse semantic rules
module K
  imports KSEQ-SYMBOLIC
  syntax K         ::= K "=>" K [klabel(#KRewrite), hook(org.kframework.kore.KRewrite)]
  // K bracket needed, e.g., Cxt[V ~> `env(E) => .`]
  syntax K         ::= "`" K "`"        [bracket]

// Sort membership not needed anymore, as we can use requires/ensures
//  syntax KItem     ::= KItem ":" KSort  [hook]
endmodule


module BUBBLE

  syntax Bubble ::= BubbleItem Bubble [token]
                  | BubbleItem        [token]
  syntax BubbleItem ::= r"((?!rule|syntax|endmodule|configuration|context)\\S+)" [token]
                         // the proper way to reject would be: reject("rule|syntax|endmodule|configuration|context")

endmodule

// To be used for first-level parsing/pretty-printing of global KORE
// definitions, where the K terms are put in bubbles.  A similar, but
// larger OUTER module can be defined for arbitrary K definitions.
module OUTER-KORE
  imports BASIC-K
  imports BUBBLE

  syntax KDefinition   ::= KRequireList KModuleList
                               [klabel(#KDefinition), hook(org.kframework.kore.outer.Definition)]

  syntax KRequire      ::= "require" KString
                               [klabel(#KRequire), hook(org.kframework.kore.outer.Require)]

  syntax KRequireList  ::= ""  [klabel(#emptyKRequireList), onlyLabel]
                         | KRequire KRequireList
                               [klabel(#KRequireList), assoc, comm, unit(#emptyKRequireList)]

  syntax KModule       ::= "module" KModuleName KAttributesDeclaration
                                    KImportList
                                    KSentenceList
                           "endmodule"
                               [klabel(#KModule), hook(org.kframework.kore.outer.Module)]
  syntax KModuleList   ::= ""  [klabel(#emptyKModuleList), onlyLabel]
                         | KModule KModuleList
                               [klabel(#KModuleList), assoc, comm, unit(#emptyKModuleList)]

  syntax KImport       ::= "imports" KModuleName
                               [klabel(#KImport), hook(org.kframework.kore.outer.Import)]
  syntax KImportList   ::= ""  [klabel(#emptyKImportList), onlyLabel]
                         | KImport KImportList
                               [klabel(#KImportList), assoc, comm, unit(#emptyKImportList)]

  syntax KSentenceList ::= ""  [klabel(#emptyKSentenceList), onlyLabel]
                         | KSentence KSentenceList
                               [klabel(#KSentenceList), assoc, comm, unit(#kemptyKSentenceList)]

  syntax KSentence ::= "syntax" KSort KAttributesDeclaration
                               [klabel(#KSyntaxSort), hook(org.kframework.kore.outer.SyntaxSort)]
                     | "syntax" KSort "::=" KProduction KAttributesDeclaration
                               [klabel(#KSyntaxProduction), hook(org.kframework.kore.outer.SyntaxProduction)]
                     | "syntax" "priority"   KPrioritySeq KAttributesDeclaration
                               [klabel(#KSyntaxPriority), hook(org.kframework.kore.outer.SyntaxPriority)]
                     | "syntax" "priorities" KPrioritySeq KAttributesDeclaration
                               [klabel(#KSyntaxPriority), hook(org.kframework.kore.outer.SyntaxPriority)]

  syntax KPrioritySeq ::= KNeTagSet ">" KPrioritySeq   [klabel(#KPrioritySeq), assoc]
                        | KNeTagSet                    [klabel(#KPrioritySeq)]
  syntax KNeTagSet    ::= Tag KNeTagSet                [klabel(#KTagSet), assoc, comm]
                        | Tag                          [klabel(#KTagSet)]
  syntax Tag ::= KLabel

  syntax KProduction ::= ""    [klabel(#emptyKProduction), onlyLabel]
                       | KProductionItem KProduction
                               [klabel(#KProduction), assoc, unit(#emptyKProduction)]
  syntax KProductionItem ::= KSort       [hook(org.kframework.kore.outer.NonTerminal)]
                           | KString     [hook(org.kframework.kore.outer.Terminal)]
                           | "r" KString [hook(org.kframework.kore.outer.RegexTerminal)]

  // We use #KAttributes as top KLabel in the K term holding the attributes
  syntax KAttributesDeclaration ::= ""        [klabel(#NoKAttributesDeclaration)]
                                  | "[" K "]" // TODO: work this out since we would like to keep the current way of parsing attributes
                                              [klabel(#KAttributesDeclaration), hook(org.kframework.kore.KAttributes)]
  syntax KSentence ::= "configuration" Contents
                               [klabel(#KConfiguration), hook(org.kframework.kore.outer.Configuration)]
                     | "rule"    Contents
                               [klabel(#KRule), hook(org.kframework.kore.outer.Rule)]
                     | "context" Contents
                               [klabel(#KContext), hook(org.kframework.kore.outer.Context)]
  syntax Contents ::= Bubble                        [klabel(#NoAttrs)]
                    | Bubble KAttributesDeclaration [klabel(#Attrs), prefer]
  // The following can still change
  syntax KModuleName ::= r"[A-Z][A-Z\\-]*"    [token]
  syntax KSort       ::= r"[A-Z][A-Za-z0-9]*" [token, hook(org.kframework.kore.outer.Sort)]
endmodule


module KORE
  imports OUTER-KORE
  imports K
  imports BUBBLE
endmodule
