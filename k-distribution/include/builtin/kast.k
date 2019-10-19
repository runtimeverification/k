// Copyright (c) 2015-2019 K Team. All Rights Reserved.

// Module defining only the sorts K and KString, useful for modularity
module SORT-K
  syntax K [hook(K.K)]
endmodule

module BASIC-K
  imports ML-SYNTAX
  syntax KItem [hook(K.KItem)]
  syntax K     ::= KItem
  syntax KConfigVar [token]
endmodule

module KSTRING
  syntax KString ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]
  // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
endmodule

module BUILTIN-ID-TOKENS
  syntax #LowerId ::= r"[a-z][a-zA-Z0-9]*"                    [prec(2), token]
  syntax #UpperId ::= r"[A-Z][a-zA-Z0-9]*"                    [prec(2), token]
endmodule

module SORT-KBOTT
  imports SORT-K
  syntax KBott
endmodule

module KAST
  imports BASIC-K
  imports SORT-KBOTT
  imports KSTRING
  imports BUILTIN-ID-TOKENS

  syntax KBott ::= "#token" "(" KString "," KString ")"  [klabel(#KToken), symbol]
                 | "#klabel" "(" KLabel ")"              [klabel(#WrappedKLabel), symbol]
                 | KLabel "(" KList ")"                  [klabel(#KApply), symbol]
  syntax KItem ::= KBott

  syntax KLabel ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\n\\r])+`" [token]
                  | #LowerId                                   [token, autoReject]
                  | r"(?<![a-zA-Z0-9])[#a-z][a-zA-Z0-9]*"               [token, autoReject, prec(1)]
                       // something that doesn't collide with meta-variables

  syntax KList ::= K
                 | ".KList"          [klabel(#EmptyKList), symbol]
                 | ".::KList"        [klabel(#EmptyKList), symbol]
                 | KList "," KList   [klabel(#KList), left, assoc, unit(#EmptyKList), symbol, prefer]
endmodule


// To be used when parsing/pretty-printing ground configurations
module KSEQ
  imports KAST
  imports K-TOP-SORT
  syntax K ::= ".K"      [klabel(#EmptyK), symbol, unparseAvoid]
             | "."       [klabel(#EmptyK), symbol]
             | ".::K"    [klabel(#EmptyK), symbol, unparseAvoid]
  syntax K ::= K "~>" K  [klabel(#KSequence), left, assoc, unit(#EmptyK), symbol]
  syntax left #KSequence
  syntax {Sort} Sort     ::= "(" Sort ")"    [bracket]
endmodule

module ML-SYNTAX
  imports SORT-K

  syntax #KVariable

  syntax {Sort} Sort ::= "#True" [klabel(#True), symbol, mlUnary]
                       | "#False" [klabel(#False), symbol, mlUnary]
                       | "#Not" "(" Sort ")" [klabel(#Not), symbol, mlOp, mlUnary]

  syntax {Sort1, Sort2} Sort2 ::= "#Ceil" "(" Sort1 ")" [klabel(#Ceil), symbol, mlOp, mlUnary]
                                | "#Floor" "(" Sort1 ")" [klabel(#Floor), symbol, mlOp, mlUnary]
                                | "{" Sort1 "#Equals" Sort1 "}" [klabel(#Equals), symbol, mlOp, mlEquals, format(%1%i%n%2%d%n%3%i%n%4%d%n%5)]

  syntax priorities mlUnary > mlEquals > mlAnd

  syntax {Sort} Sort ::= Sort "#And" Sort [klabel(#And), symbol, assoc, left, comm, unit(#True), mlOp, mlAnd, format(%i%1%d%n%2%n%i%3%d)]
                       > Sort "#Or" Sort [klabel(#Or), symbol, assoc, left, comm, unit(#False), mlOp, format(%i%1%d%n%2%n%i%3%d)]
                       > Sort "#Implies" Sort [klabel(#Implies), symbol, mlOp, mlImplies, format(%i%1%d%n%2%n%i%3%d)]

  syntax priorities mlImplies > mlQuantifier

  syntax {Sort1, Sort2} Sort2 ::= "#Exists" Sort1 "." Sort2 [klabel(#Exists), symbol, mlOp, mlBinder, mlQuantifier]
                                | "#Forall" Sort1 "." Sort2 [klabel(#Forall), symbol, mlOp, mlBinder, mlQuantifier]

  syntax {Sort} Sort ::= "#AG" "(" Sort ")" [klabel(#AG), symbol, mlOp, mlQuantifier]
                       | "#wEF" "(" Sort ")" [klabel(weakExistsFinally), symbol, mlOp, mlQuantifier]
endmodule

// To be used when parsing/pretty-printing symbolic configurations
module KSEQ-SYMBOLIC
  imports KSEQ
  imports ML-SYNTAX

  syntax #KVariable ::= r"(?<![A-Za-z0-9_\\$!\\?@])(\\!|\\?|@)?([A-Z][A-Za-z0-9'_]*|_)"   [token, prec(1), autoReject]
                      | #UpperId                                                          [token, autoReject]
  syntax KConfigVar ::= r"(?<![A-Za-z0-9_\\$!\\?@])(\\$)([A-Z][A-Za-z0-9'_]*)"            [token, autoReject]
  syntax KBott      ::= #KVariable
  syntax KBott      ::= KConfigVar
  syntax KLabel     ::= #KVariable
endmodule

module KCELLS
  imports KAST

  syntax Cell
  syntax Bag ::= Bag Bag  [left, assoc, klabel(#cells), symbol, unit(#cells)]
               | ".Bag"   [klabel(#cells), symbol]
               | ".::Bag" [klabel(#cells), symbol]
               | Cell
  syntax Bag ::= "(" Bag ")" [bracket]
  syntax K ::= Bag
  syntax #RuleBody ::= "[" "[" K "]" "]" Bag    [klabel(#withConfig), symbol, avoid]
  syntax non-assoc #withConfig
  syntax Bag ::= KBott
endmodule

module RULE-CELLS
  imports KCELLS
  imports RULE-LISTS
  // if this module is imported, the parser automatically
  // generates, for all productions that have the attribute 'cell' or 'maincell',
  // a production like below:
  //syntax Cell ::= "<top>" #OptionalDots K #OptionalDots "</top>" [klabel(<top>)]

  syntax #OptionalDots ::= "..." [klabel(#dots), symbol]
                         | ""    [klabel(#noDots), symbol]
endmodule

module CONFIG-CELLS
  imports KCELLS
  imports RULE-LISTS
  syntax #CellName ::= r"[a-zA-Z][a-zA-Z0-9\\-]*"  [token, prec(1)]
                     | #LowerId            [token]
                     | #UpperId            [token]

  syntax Cell ::= "<" #CellName #CellProperties ">" K "</" #CellName ">" [klabel(#configCell), symbol]
  syntax Cell ::= "<" #CellName "/>" [klabel(#externalCell), symbol]

  syntax #CellProperties ::= #CellProperty #CellProperties [klabel(#cellPropertyList), symbol]
                           | ""                            [klabel(#cellPropertyListTerminator), symbol]
  syntax #CellProperty ::= #CellName "=" KString           [klabel(#cellProperty), symbol]

endmodule


module REQUIRES-ENSURES
  imports BASIC-K

  syntax #RuleBody ::= K

  syntax #RuleContent ::= #RuleBody                                 [klabel("#ruleNoConditions"), symbol]
                        | #RuleBody "requires" K                    [klabel("#ruleRequires"), symbol]
                        | #RuleBody "when" K                        [klabel("#ruleRequires"), symbol]
                        | #RuleBody "ensures"  K                    [klabel("#ruleEnsures"), symbol]
                        | #RuleBody "requires" K "ensures" K        [klabel("#ruleRequiresEnsures"), symbol]
                        | #RuleBody "when" K "ensures" K            [klabel("#ruleRequiresEnsures"), symbol]
endmodule

module K-TOP-SORT
  imports SORT-KBOTT
  syntax KItem ::= KBott
  syntax {Sort} KItem ::= Sort
endmodule

module K-BOTTOM-SORT
  imports SORT-KBOTT
  syntax KItem ::= KBott
  syntax {Sort} Sort ::= KBott
endmodule

module K-SORT-LATTICE
  imports K-TOP-SORT
  imports K-BOTTOM-SORT
endmodule

module AUTO-CASTS
  // if this module is imported, the parser automatically
  // generates, for all sorts, productions of the form:
  // Sort  ::= Sort "::Sort"
  // Sort  ::= Sort ":Sort"
  // KBott ::= Sort "<:Sort"
  // Sort  ::= K    ":>Sort"
  // this is part of the mechanism that allows concrete user syntax in K
endmodule

module AUTO-FOLLOW
  // if this module is imported, the parser automatically
  // generates a follow restriction for every terminal which is a prefix
  // of another terminal. This is useful to prevent ambiguities such as:
  // syntax K ::= "a"
  // syntax K ::= "b"
  // syntax K ::= "ab"
  // syntax K ::= K K
  // #parse("ab", "K")
  // In the above example, the terminal "a" is not allowed to be followed by a "b"
  // because it would turn the terminal into the terminal "ab".
endmodule

module PROGRAM-LISTS
  imports SORT-K
  // if this module is imported, the parser automatically
  // replaces the default productions for lists:
  // Es ::= E "," Es [userList("*"), klabel('_,_)]
  //      | ".Es"    [userList("*"), klabel('.Es)]
  // into a series of productions more suitable for programs:
  // Es#Terminator ::= ""      [klabel('.Es)]
  // Ne#Es ::= E "," Ne#Es     [klabel('_,_)]
  //         | E Es#Terminator [klabel('_,_)]
  // Es ::= Ne#Es
  //      | Es#Terminator      // if the list is *
endmodule

module RULE-LISTS
  // if this module is imported, the parser automatically
  // adds the subsort production to the parsing module only:
  // Es ::= E        [userList("*")]

endmodule

module DEFAULT-LAYOUT
    syntax #Layout ::= r"(\\/\\*([^\\*]|(\\*+([^\\*\\/])))*\\*+\\/)"
                     | r"(\\/\\/[^\\n\\r]*)"
                     | r"([\\ \\n\\r\\t])"
endmodule

module DEFAULT-CONFIGURATION
  imports BASIC-K

  configuration <k> $PGM:K </k>
endmodule

module RECORD-PRODUCTIONS
  // if this module is imported, prefix productions of the form
  // syntax Sort ::= name(Args)
  // will be able to be parsed with don't-care variables according
  // to their nonterminal's names
endmodule

// To be used to parse semantic rules
module K
  imports KSEQ-SYMBOLIC
  imports REQUIRES-ENSURES
  imports RECORD-PRODUCTIONS
  imports K-SORT-LATTICE
  imports AUTO-CASTS
  imports AUTO-FOLLOW

  syntax {Sort} Sort ::= Sort "=>" Sort [klabel(#KRewrite), symbol]
  syntax non-assoc #KRewrite
  syntax priority #KRewrite > #withConfig

  syntax {Sort} Sort ::= Sort "#as" Sort [klabel(#KAs), symbol]
  // functions that preserve sorts and can therefore have inner rewrites
  syntax {Sort} Sort ::= "#fun" "(" Sort ")" "(" Sort ")" [klabel(#fun2), symbol, prefer]
  // functions that do not preserve sort and therefore cannot have inner rewrites
  syntax {Sort1, Sort2} Sort1 ::= "#fun" "(" Sort2 "=>" Sort1 ")" "(" Sort2 ")" [klabel(#fun3), symbol]

  /*@ Set membership over terms. In addition to equality over
      concrete patterns, K also supports computing equality
      between a concrete pattern and a symbolic pattern.
      This is compiled efficiently down to pattern matching,
      and can be used by putting a term with unbound variables
      in the left child of :=K or =/=K. Note that this does not
      bind variables used on the lhs however (although this may
      change in the future).*/

  syntax Bool ::= left:
                  K ":=K" K           [function, functional, klabel(_:=K_), symbol, equalEqualK]
                | K ":/=K" K          [function, functional, klabel(_:/=K_), symbol, notEqualEqualK]
endmodule

// To be used to parse terms in full K
module K-TERM
  imports KSEQ-SYMBOLIC
  imports RECORD-PRODUCTIONS
  imports K-SORT-LATTICE
  imports AUTO-CASTS
  imports AUTO-FOLLOW
endmodule
