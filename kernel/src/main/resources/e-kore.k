// Copyright (c) 2015 K Team. All Rights Reserved.

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

  syntax KLabel ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\s])+`" [token, hook(org.kframework.kore.KLabel)]
                  | r"[#a-z][a-zA-Z0-9]*"
                       [token, hook(org.kframework.kore.KLabel)]
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
                           [token, hook(org.kframework.kore.KVariable)]
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

  syntax Bubble ::= Bubble BubbleItem [token]
                  | BubbleItem        [token]
  syntax BubbleItem ::= r"((?!rule|syntax|endmodule|configuration|context)\\S+)" [token]
                         // the proper way to reject would be: reject("rule|syntax|endmodule|configuration|context")

endmodule

module ATTRIBUTES
  imports BASIC-K
  syntax KEY        ::= r"[a-z][A-Za-z\\-0-9]*" [token]
  syntax TAGList    ::= TAGCONTENT              [token]
  syntax TAGCONTENT ::= TAGCONTENT TC           [klabel(#TAGCONTENTList)] // dummy klabel
                      | TC                      [klabel(#TAGCONTENTTC)]   // dummy klabel
                      | ""                      [klabel(#NOTAGCONTENT)]   // dummy klabel
  syntax TC ::= r"[^\\n\\r\\(\\)\\\"]+"         [klabel('TC)]             // dummy klabel
              | "(" TAGCONTENT ")"

  syntax Attr ::= KEY                 [klabel(#TagSimple)]
                | KEY "(" TAGList ")" [klabel(#TagContent)]
                | KEY "(" KString ")" [klabel(#TagString)]
endmodule

// To be used for first-level parsing/pretty-printing of global KORE
// definitions, where the K terms are put in bubbles.  A similar, but
// larger OUTER module can be defined for arbitrary K definitions.
module OUTER-KORE
  imports BASIC-K
  imports BUBBLE
  imports ATTRIBUTES

  syntax KDefinition   ::= KRequireList KModuleList
                               [klabel(#KDefinition), hook(org.kframework.definition.Definition)]

  syntax KRequire      ::= "require" KString
                               [klabel(#KRequire), hook(org.kframework.definition.Require)]

  syntax KRequireList  ::= ""  [klabel(#emptyKRequireList), onlyLabel]
                         | KRequireList KRequire
                               [klabel(#KRequireList), assoc, comm, unit(#emptyKRequireList)]

  syntax KModule       ::= "module" KModuleName OptionalAttributes
                                    KImportList
                                    KSentenceList
                           "endmodule"
                               [klabel(#KModule), hook(org.kframework.definition.Module)]
  syntax KModuleList   ::= ""  [klabel(#emptyKModuleList), onlyLabel]
                         | KModuleList KModule
                               [klabel(#KModuleList), assoc, comm, unit(#emptyKModuleList)]

  syntax KImport       ::= "imports" KModuleName
                               [klabel(#KImport), hook(org.kframework.definition.Import)]
  syntax KImportList   ::= ""  [klabel(#emptyKImportList), onlyLabel]
                         | KImportList KImport
                               [klabel(#KImportList), assoc, comm, unit(#emptyKImportList)]

  syntax KSentenceList ::= ""  [klabel(#emptyKSentenceList), onlyLabel]
                         | KSentenceList KSentence
                               [klabel(#KSentenceList), assoc, comm, unit(#kemptyKSentenceList)]

  syntax KSentence ::= "syntax" KSort OptionalAttributes
                               [klabel(#KSyntaxSort), hook(org.kframework.definition.SyntaxSort)]
                     | "syntax" KSort "::=" PrioritySeqBlock
                               [klabel(#KSyntaxProduction), hook(org.kframework.definition.SyntaxProduction)]
                     | "syntax" "priority"   KPrioritySeq OptionalAttributes
                               [klabel(#KSyntaxPriority), hook(org.kframework.definition.SyntaxPriority)]
                     | "syntax" "priorities" KPrioritySeq OptionalAttributes
                               [klabel(#KSyntaxPriorities), hook(org.kframework.definition.SyntaxPriority)]
                     | "syntax" "left" KNeTagSet OptionalAttributes
                               [klabel(#KSyntaxLeft), hook(org.kframework.definition.SyntaxPriority)]
                     | "syntax" "right" KNeTagSet OptionalAttributes
                               [klabel(#KSyntaxRight), hook(org.kframework.definition.SyntaxPriority)]
                     | "syntax" "non-assoc" KNeTagSet OptionalAttributes
                               [klabel(#KSyntaxNonAssoc), hook(org.kframework.definition.SyntaxPriority)]

  syntax KPrioritySeq ::= KPrioritySeq ">" KNeTagSet   [klabel(#KPrioritySeq), assoc]
                        | KNeTagSet
  syntax KNeTagSet    ::= Tag KNeTagSet                [klabel(#KTagSet), assoc, comm]
                        | Tag
  syntax Tag ::= KLabel

  syntax KProduction ::= KProductionItem
                       | KProduction KProductionItem
                               [klabel(#KProduction), assoc, unit(#emptyKProduction)]
  syntax KProductionItem ::= KSort       [hook(org.kframework.definition.NonTerminal)]
                           | KString     [hook(org.kframework.definition.Terminal)]
                           | "r" KString [hook(org.kframework.definition.RegexTerminal)]
                           | "Token" "{" TokenContent "}" [klabel(#KPIToken)]
                           | "Lexer" "{" TokenContent "}" [klabel(#KPILexer)]
                           | "NeList" "{" KSort "," KString "}" [klabel(#NeList)]
                           |   "List" "{" KSort "," KString "}" [klabel(#List)]
  syntax TokenContent ::= r"[^\\n\\r}]" [token]
  syntax PrioritySeqBlock ::= PrioritySeqBlock ">" AssocAttribute ProdBlock [klabel(#PrioritySeqBlock)]
                            | ProdBlock
  syntax AssocAttribute ::= ""           [klabel(#NoAttribute)]
                          | "left:"      [klabel(#LeftAttribute)]
                          | "right:"     [klabel(#RightAttribute)]
                          | "non-assoc:" [klabel(#NonAssocAttribute)]
  syntax ProdBlock ::= ProdBlock "|" KProductionWAttr [klabel(#ProdBlock)]
                     | KProductionWAttr
  syntax KProductionWAttr ::= KProduction OptionalAttributes [klabel(#KProductionWAttr)]
                            | KLabel "(" KSortList ")" OptionalAttributes [klabel(#KFuncProductionWAttr)]
                            |        "(" KSortList ")" OptionalAttributes [klabel(#KTupleProductionWAttr)]
  syntax KSortList ::= KSortList "," KSort [klabel(#KSortList)]
                     | KSort
  // We use #KAttributes as top KLabel in the K term holding the attributes
  syntax OptionalAttributes ::= KAttributesDeclaration
                              | "" [klabel(#NoKAttributesDeclaration)]
  syntax KAttributesDeclaration ::= "[" AttrList "]" [klabel(#KAttributesDeclaration), hook(org.kframework.kore.KAttributes)]
  syntax AttrList ::= AttrList "," Attr [klabel(#KAttributesList)]
                    | Attr

  syntax KSentence ::= "configuration" Contents
                               [klabel(#KConfiguration), hook(org.kframework.definition.Configuration)]
                     | "rule"    Contents
                               [klabel(#KRule), hook(org.kframework.definition.Rule)]
                     | "context" Contents
                               [klabel(#KContext), hook(org.kframework.definition.Context)]
  syntax Contents ::= Bubble                        [klabel(#NoAttrs)]
                    | Bubble KAttributesDeclaration [klabel(#Attrs), prefer]
  // The following can still change
  syntax KModuleName ::= r"[A-Z][A-Z\\-]*"    [token]
  syntax KSort       ::= r"[A-Z][A-Za-z0-9]*" [token, hook(org.kframework.definition.Sort)]
endmodule


module KORE
  imports OUTER-KORE
  imports K
  imports BUBBLE
endmodule
