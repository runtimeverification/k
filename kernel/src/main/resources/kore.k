// Copyright (c) 2014-2015 K Team. All Rights Reserved.

/*
This defines the syntax of KORE.  See
  https://github.com/kframework/k/wiki/KAST-and-KORE
for explanations about what KORE is and how to desugar full K into KORE.

Below we prefer to modularize the syntax in a way that each module can be
used in some parsing situation, which is also briefly described before the
module.

Everything is Meta- at this level, so we dropped the Meta everywhere.

Known issues:
- The attributes do not yet parse as K terms.
- The syntax of KORE below uses more than just KORE, for ease of reading.
*/



// Module defining only the sorts K and KString, useful for modularity
module BASIC-K
  syntax K   //[...]   // no constructors at this stage
  syntax KString ::= r"[\\\"]([^\\\"\\n\\r\\\\]|[\\\\][nrtf\\\"\\\\])*[\\\"]"
    [token, noAutoReject, onlyLabel, hook(org.kframework.koreimplementation.KString)]
    // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
endmodule



// To be used when parsing/pretty-printing programs in KAST format
// (e.g., programs parsed and then output by an external parser)
module KAST
  imports BASIC-K
  syntax K     ::= KItem
  syntax KItem ::= "#token" "(" KString "," KString ")"
    [ klabel(#KToken), hook(org.kframework.koreimplementation.KToken) ]
  syntax KItem ::= "#klabel" "(" KLabel ")"
    [ klabel(#WrappedKLabel), hook(org.kframework.koreimplementation.meta.WrappedKLabel) ]
  syntax KItem ::= KLabel "(" KList ")"
    [ klabel(#KApply), hook(org.kframework.koreimplementation.KApply) ]

  syntax KLabel ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\s])+`"
    [ klabel(#KLabel), token ] // everything except `, unless escaped \`
  syntax KLabel ::= r"[#a-z][a-zA-Z0-9]*"
    [ klabel(#KLabel), token, hook(org.kframework.koreimplementation.KLabel) ]
    // something that doesn't collide with meta-variables

  syntax KList ::= K
  syntax KList ::= ".::KList"
    [ klabel(#EmptyKList), hook(org.kframework.koreimplementation.EmptyKList) ]
  syntax KList ::= KList "," KList
    [ klabel(#KList), left, assoc, unit(#EmptyKList), hook(org.kframework.koreimplementation.KList) ]
endmodule



// To be used when parsing/pretty-printing ground configurations
module KSEQ
  imports KAST
  syntax K     ::= ".::K"
    [ klabel(#EmptyK), hook(org.kframework.koreimplementation.EmptyK) ]
  syntax K     ::= K "~>" K
    [ klabel(#KSequence), left, assoc, unit(#EmptyK), hook(org.kframework.koreimplementation.KSequence) ]
endmodule



// To be used when parsing/pretty-printing symbolic configurations
module KSEQ-SYMBOLIC
  imports KSEQ
  syntax KVariable ::= r"(?<![A-Za-z0-9\\_])(\\$|\\!|\\?)?([A-Z][A-Za-z0-9']*|_)"
    [ hook(org.kframework.koreimplementation.KVariable) ] // same like KSort?
  syntax KItem     ::= KVariable
  syntax KLabel    ::= KVariable
endmodule



// To be used to parse semantic rules
module K
  imports KSEQ-SYMBOLIC
  syntax K         ::= K "=>" K
    [ klabel(#KRewrite), hook(org.kframework.koreimplementation.KRewrite) ]
  // K bracket needed, e.g., Cxt[V ~> `env(E) => .`]
  syntax K         ::= "`" K "`"        [ bracket ]

// Sort membership not needed anymore, as we can use requires/ensures
//  syntax KItem     ::= KItem ":" KSort  [ hook ]
endmodule



// To be used for first-level parsing/pretty-printing of global KORE
// definitions, where the K terms are put in bubbles.  A similar, but
// larger OUTER module can be defined for arbitrary K definitions.
module OUTER-KORE
  imports BASIC-K

  syntax KDefinition   ::= KRequireList KModuleList
    [ klabel(#KDefinition), hook(org.kframework.koreimplementation.outer.Definition) ]

  syntax KRequire      ::= "require" KString
    [ klabel(#KRequire), hook(org.kframework.koreimplementation.outer.Require) ]

  // Radu says: The list declarations below are a bit tricky (no separator,
  // and the empty element is null).
  // Grigore wants to have a semantic declaration of the type
  // L ::= L L [assoc] but when the list can be nullable (has the
  // production ""), then this goes into an infinite parsing cycle.
  // My fix is to declare the list as L ::= LItem L | "".
  // Grigore is right in saying that it looks weird when we want to match
  // somewhere in the middle of the list.
  // Another format to take into consideration would be the
  // L ::= List{LItem,""}, but this complicates KORE, and we would
  // like to keep this at a minimum.
  // So are associative lists something different enough to deserve
  // special treatment?
  //
  // Grigore says:  This is an implementation detail/limitation of the
  // current parser, and we should fix it at that level instead of
  // driving the design of the language around it.
  // Even if we adopt the special notation L ::= List{LItem,""}, you
  // still have the same problem, that the list sort L is nullable.
  // It allows you to cheat, by generating and parsing with
  // L ::= LItem L | "" instead, but you would still have the problem
  // of matching in the middle of a list: L1:L I:LItem L2:L.
  // So I dislike the changes you made below, Radu, but I accept them
  // for now in order to move on with the incorporation of KORE
  // before you fix the parsing problem with nullable sorts.
  // But the main circular parsing problem still needs to be solved.

  syntax KRequireList  ::= KRequire KRequireList
    [ klabel(#KRequireList), assoc, comm, unit(#emptyKRequireList) ]
  syntax KRequireList  ::= ""
    [ klabel(#emptyKRequireList), onlyLabel]

  syntax KModule       ::= "module" KModuleName KAttributesDeclaration
                                    KImportList
                                    KSentenceList
                           "endmodule"
    [ klabel(#KModule), hook(org.kframework.koreimplementation.outer.Module) ]
  syntax KModuleList   ::= KModule KModuleList
    [ klabel(#KModuleList), assoc, comm, unit(#emptyKModuleList) ]
  syntax KModuleList   ::= ""
    [ klabel(#emptyKModuleList), onlyLabel]

  syntax KImport       ::= "imports" KModuleName
    [ klabel(#KImport), hook(org.kframework.koreimplementation.outer.Import) ]
  syntax KImportList   ::= KImport KImportList
    [ klabel(#KImportList), assoc, comm, unit(#emptyKImportList) ]
  syntax KImportList   ::= ""
    [ klabel(#emptyKImportList), onlyLabel]

  syntax KSentenceList ::= KSentence KSentenceList
    [ klabel(#KSentenceList), assoc, comm, unit(#kemptyKSentenceList) ]
  syntax KSentenceList ::= ""
    [ klabel(#emptyKSentenceList), onlyLabel]

  syntax KSentence ::= "syntax" KSort KAttributesDeclaration
    [ klabel(#KSyntaxSort), hook(org.kframework.koreimplementation.outer.SyntaxSort) ]
  syntax KSentence ::= "syntax" KSort "::=" KProduction KAttributesDeclaration
    [ klabel(#KSyntaxProduction), hook(org.kframework.koreimplementation.outer.SyntaxProduction) ] ]
  syntax KSentence ::= "syntax" "priority" KString ">" KString KAttributesDeclaration
    [ klabel(#KSyntaxPriority), hook(org.kframework.koreimplementation.outer.SyntaxPriority) ]
    // TYhe above should be changed to allow partial orders between lists of KLabels
    // in order to avoid the quadratic explosion of the translation from K to KORE

// Configuration declarations not needed anymore, as it can be replaced
// with existing KORE plus conventions; see Wiki mentioned above
//  syntax KSentence ::= "configuration" K "requires" K             KAttributesDeclaration
//    [ klabel(#KConfiguration), hook(org.kframework.koreimplementation.outer.Configuration) ]

  syntax KSentence ::= "rule"    K "requires" K "ensures" K KAttributesDeclaration
    [ klabel(#KRule), hook(org.kframework.koreimplementation.outer.Rule) ]
  syntax KSentence ::= "context" K "requires" K             KAttributesDeclaration
    [ klabel(#KContext), hook(org.kframework.koreimplementation.outer.Context) ]

  syntax KProduction ::= ""
    [ klabel(#emptyKProduction), onlyLabel]
  syntax KProduction ::= KProductionItem KProduction
    [ klabel(#KProduction), assoc, unit(#emptyKProduction) ]
  syntax KProductionItem ::= KSort
    [ hook(org.kframework.koreimplementation.outer.NonTerminal) ] // non-terminal
  syntax KProductionItem ::= KString
    [ hook(org.kframework.koreimplementation.outer.Terminal) ]    // terminals, including regexes
  syntax KProductionItem ::= "r" KString
    [ hook(org.kframework.koreimplementation.outer.RegexTerminal) ]    // terminals, including regexes

  // We use #KAttributes as top KLabel in the K term holding the attributes
  syntax KAttributesDeclaration ::= "[" K "]"
    [ klabel(#KAttributesDeclaration), hook(org.kframework.koreimplementation.KAttributes) ]

  // The following can still change
  syntax KModuleName ::= r"[A-Z][A-Z\\-]*"
    [ token ]
  syntax KSort       ::= r"[A-Z][A-Za-z0-9]*"
    [ token, hook(org.kframework.koreimplementation.outer.Sort) ]
endmodule



module KORE
  imports OUTER-KORE
  imports K
endmodule