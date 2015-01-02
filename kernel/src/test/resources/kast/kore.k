// Copyright (c) 2014-2015 K Team. All Rights Reserved.

/*
This defines a core subset of K and KAST, called KORE, with the property
that any KAST definition, and thus any K definition, can be mechanically
translated to a definition using only this minimal subset.  An additional
property of KORE is that we do not want to lose anything from the original
definition.  For example, we do not want to lose the capability to pretty
print terms based on the original syntax, or the capability to report error
messages referring to constructs in the original definition.

We selected this core of K based on the following two criteria:

(1) We want to support everything that KORE contains

(2) Everything we support can be easily expressed in KORE

(3) It is minimal with properties (1) and (2)
*/

// Everything is Meta- at this level, so I dropped the Meta everywhere

/*
  The "hook" attribute has the following semantics:
  1. Hooks are relative to the hookNamespace module attribute.
  2. "hook(Foo)" will hook to the constructor named Foo with the arguments being
     the non-terminals of the production.
  3. "hook" is shorthand for hooking to a constructor which has the same name as
     the sort of the current production.
*/

// Known issue: The attributes do not yet parse as K terms

// Recall that in KORE productions must have one of the attributes klabel, token, bracket



// Module defining only the sorts K and KString, useful for modularity
module BASIC-K
  syntax K   //[...]   // no constructors at this stage
  syntax KString ::= r"[\\\"]([^\\\"\\n\\r\\\\]|[\\\\][nrtf\\\"\\\\])*[\\\"]"   [token, noAutoReject, onlyLabel]
         // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
endmodule



// To be used when parsing programs in KAST format
// (e.g., programs parsed and then output by an external parser)
module KAST //[ hookNamespace(org.kframework.kore) ]  // the hook will probably change
  imports BASIC-K
  syntax K     ::= KItem                                 //[ ... ]

  syntax KItem  ::= "#token" "(" KString "," KString ")"  [ klabel(#KToken), hook ]
  // @cos proposes to eliminate the next injection, and instead to allow
  // the use of meta-level KAST in definitions: #KApply(#token("_+_","KLabel"),#KList(1,3))
  // @grosu is sceptic: that would imply to allow KAST syntax in programs; not worth the price
  syntax KItem ::= "#klabel" "(" KLabel ")"              [ klabel(#KLabel), hook(org.kframework.kore.KItem) ]
  syntax KItem ::= KLabel "(" KList ")"                  [ klabel(#KApply), hook(org.kframework.kore.KItem) ]

  syntax KLabel ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\s])+`"   [ token, hook ] // everything except `, unless escaped \`
  syntax KLabel ::= r"[#a-z][a-zA-Z0-9]*"                [ token, hook ] // something that doesn't collide with meta-variables
// KLabel brackets not needed if @cos' approach above works
//  syntax KLabel ::= "`" KLabel "`"   [ bracket, hook ]

  syntax KList ::= K                //[...]
  syntax KList ::= ".::KList"       [klabel(#emptyKList)]
  syntax KList ::= KList "," KList  [klabel(#KList), left, assoc, unit(#emptyKList)]
endmodule



// To be used when pretty-printing stuck computations
module KSEQ
  imports KAST
  syntax K     ::= ".::K"                                [ klabel(#emptyK) ]
  syntax K     ::= K "~>" K                              [ klabel(#KSequence), left, assoc, unit(#emptyK) ]
endmodule



// To be used to parse semantic rules
module K
  imports KSEQ
  syntax KVariable ::= r"(?<![A-Za-z0-9\\_])(\\$|\\!|\\?)?([A-Z][A-Za-z0-9']*|_)" [ hook ] // same like KSort?
  syntax KItem     ::= KVariable        //[ ... ]
  syntax KLabel    ::= KVariable        //[ ... ]
  syntax K         ::= K "=>" K         [ klabel(#KRewrite), hook(Rewrite) ]
  // K bracket needed, e.g., Cxt[V ~> `env(E) => .`]
  syntax K         ::= "`" K "`"        [ bracket ]

// Sort membership not needed anymore, as we can use requires/ensures
//  syntax KItem     ::= KItem ":" KSort  [ hook ]
endmodule



// To be used for first-level parsing of global KORE definitions,
// where the K terms are put in bubbles.  A similar, but larger
// module can be defined for global KAST definitions.
module OUTER-KORE //[ hookNamespace(org.kframework.kore.outer) ]
  imports BASIC-K

  syntax KDefinition   ::= KRequireList KModuleList   [ hook ]

  syntax KRequire      ::= "require" KString          [ klabel(#KRequire), hook ]
  // Radu: These list declarations are a bit tricky (no separator, and the empty element is null).
  // Grigore wants to have a semantic declaration of the type L ::= L L [assoc]
  // but when the list can be nullable (has the production ""), then this goes into an infinite cycle.
  // My fix was to declare the list as L ::= LItem L | ""
  // Grigore is right in saying that it looks weird when we want to match somewhere in the middle.
  // Another format to take into consideration would be the L ::= List{LItem,""}, but this complicates KORE, and we would
  // like to keep this at a minimum. So are associative lists something different enough to deserve special treatment?
  syntax KRequireList  ::= KRequire KRequireList      [ klabel(#KRequireList), assoc, comm, unit(#emptyKRequireList) ]
  syntax KRequireList  ::= ""                         [ klabel(#emptyKRequireList), onlyLabel]

  syntax KModule       ::= "module" KModuleName KImportList KSentenceList "endmodule"  [ klabel(#KModule), hook ]
  syntax KModuleList   ::= KModule KModuleList        [ klabel(#KModuleList), assoc, comm, unit(#emptyKModuleList) ]
  syntax KModuleList   ::= ""                         [ klabel(#emptyKModuleList), onlyLabel]

  syntax KImport       ::= "imports" KModuleName    [ klabel(#KImport), hook ]
  syntax KImportList   ::= KImport KImportList      [ klabel(#KImportList), assoc, comm, unit(#emptyKImportList) ]
  syntax KImportList   ::= ""                       [ klabel(#emptyKImportList), onlyLabel]

  syntax KSentenceList ::= KSentence KSentenceList      [ klabel(#KSentenceList), assoc, comm, unit(#kemptyKSentenceList) ]
  syntax KSentenceList ::= ""                           [ klabel(#emptyKSentenceList), onlyLabel]

  syntax KSentence ::= "syntax" KSort                      KAttributesDeclaration   [ klabel(#KSentenceSyntaxSort), hook(Syntax) ]
  syntax KSentence ::= "syntax" KSort "::=" KProduction    KAttributesDeclaration   [ klabel(#KSentenceSyntaxProduction), hook(Syntax) ]
  syntax KSentence ::= "syntax" "priority"   KPrioritySeq  KAttributesDeclaration   [ klabel(#KSentenceSyntaxPriority), hook(SyntaxPriority) ]
  syntax KSentence ::= "syntax" "priorities" KPrioritySeq  KAttributesDeclaration   [ klabel(#KSentenceSyntaxPriority), hook(SyntaxPriority) ]
  syntax KSentence ::= "syntax" KAssoc KNeTagSet           KAttributesDeclaration   [ klabel(#KSentenceSyntaxAssociativity), hook(SyntaxAssociativity) ]

  syntax KAssoc    ::= "left"
  syntax KAssoc    ::= "right"
  syntax KAssoc    ::= "non-assoc"
  syntax KPrioritySeq ::= KNeTagSet ">" KPrioritySeq   [ klabel(#KPrioritySeq), assoc ]
  syntax KPrioritySeq ::= KNeTagSet                    [ klabel(#KPrioritySeq) ]
  syntax KNeTagSet    ::= Tag KNeTagSet                [ klabel(#KTagSet), assoc, comm ]
  syntax KNeTagSet    ::= Tag                          [ klabel(#KTagSet) ]
  syntax Tag ::= KLabel

  syntax KSentence ::= "configuration" K "requires" K             KAttributesDeclaration   [ klabel(#KSentenceConfiguration), hook(Configuration) ]
  syntax KSentence ::= "rule"          K "requires" K "ensures" K KAttributesDeclaration   [ klabel(#KSentenceRule), hook(Rule) ]
  syntax KSentence ::= "context"       K "requires" K             KAttributesDeclaration   [ klabel(#KSentenceContext), hook(Context) ]

  syntax KProduction ::= ""                      [ klabel(#emptyKProduction), onlyLabel]
  syntax KProduction ::= KProductionItem KProduction [ klabel(#KProduction), assoc, unit(#emptyKProduction) ]
  syntax KProductionItem ::= KSort               [ hook(NonTerminal) ] // non-terminal
  syntax KProductionItem ::= KString             [ hook(Terminal) ]    // terminals, including regexes
  syntax KProductionItem ::= "r" KString         [ hook(RegexTerminal) ]    // terminals, including regexes

  // We are going to use #KAttributes as top KLabel in the K term holding the attributes
  syntax KAttributesDeclaration ::= "[" K "]"   [ klabel(#KAttributesDeclaration), hook(KAttributes) ]

  // The following can still change
  syntax KModuleName ::= r"[A-Z][A-Z\\-]*"     [ token ]
  syntax KSort       ::= r"[A-Z][A-Za-z0-9]*"  [ token, hook ]
endmodule



module KORE
  imports OUTER-KORE
  imports K
  configuration `<k>`($PGM)  // how do I put the sort restriction for this

endmodule
