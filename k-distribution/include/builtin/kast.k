// Copyright (c) 2015-2018 K Team. All Rights Reserved.

// Module defining only the sorts K and KString, useful for modularity
module SORT-K
  syntax K [hook(K.K)]
endmodule

module BASIC-K
  imports SORT-K
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
  syntax KBott ::= ".K"      [klabel(#EmptyK), symbol, unparseAvoid]
                 | "."       [klabel(#EmptyK), symbol]
                 | ".::K"    [klabel(#EmptyK), symbol, unparseAvoid]
  syntax K ::= K "~>" K  [klabel(#KSequence), left, assoc, unit(#EmptyK), symbol]
  syntax left #KSequence
  syntax K     ::= "(" K ")"    [bracket, poly(0, 1)]
endmodule


// To be used when parsing/pretty-printing symbolic configurations
module KSEQ-SYMBOLIC
  imports KSEQ
  syntax #KVariable ::= r"(?<![A-Za-z0-9_\\$!\\?])(\\!|\\?)?([A-Z][A-Za-z0-9'_]*|_)"   [token, prec(1), autoReject]
                      | #UpperId                                                       [token, autoReject]
  syntax KConfigVar ::= r"(?<![A-Za-z0-9_\\$!\\?])(\\$)([A-Z][A-Za-z0-9'_]*)"          [token, autoReject]
  syntax KBott      ::= #KVariable
  syntax KBott      ::= KConfigVar
  syntax KLabel     ::= #KVariable

  syntax #Pattern ::= "#True" [klabel(#True), symbol]
  syntax #Pattern ::= "#False" [klabel(#False), symbol]
  syntax #Pattern ::= K
                    | #Pattern "#And" #Pattern [klabel(#And), symbol, assoc, comm, unit(#True), mlOp, format(%1 %2%n%3)]
                    > #Pattern "#Or" #Pattern [klabel(#Or), symbol, assoc, comm, unit(#False), mlOp, format(%i%1%d%n%2%n%i%3%d)]
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

  syntax RuleContent ::= K                                 [klabel("#ruleNoConditions"), symbol]
                       | K "requires" K                    [klabel("#ruleRequires"), symbol]
                       | K "when" K                        [klabel("#ruleRequires"), symbol]
                       | K "ensures"  K                    [klabel("#ruleEnsures"), symbol]
                       | K "requires" K "ensures" K        [klabel("#ruleRequiresEnsures"), symbol]
                       | K "when" K "ensures" K            [klabel("#ruleRequiresEnsures"), symbol]
endmodule

module K-TOP-SORT
  imports SORT-KBOTT
  syntax KItem ::= KBott [poly(1)]
endmodule

module K-BOTTOM-SORT
  imports SORT-KBOTT
  syntax KItem ::= KBott [poly(0)]
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

  syntax K ::= K "=>" K [klabel(#KRewrite), symbol, poly(0, 1, 2)]
  syntax non-assoc #KRewrite

  syntax K ::= K "#as" K [klabel(#KAs), symbol, poly(0, 1, 2)]
  // functions that preserve sorts and can therefore have inner rewrites
  syntax K ::= "#fun" "(" K ")" "(" K ")" [klabel(#fun2), symbol, poly(0, 1, 2), prefer]
  // functions that do not preserve sort and therefore cannot have inner rewrites
  syntax K ::= "#fun" "(" K "=>" K ")" "(" K ")" [klabel(#fun3), symbol, poly(0, 2; 1, 3)]
endmodule

// To be used to parse terms in full K
module K-TERM
  imports KSEQ-SYMBOLIC
  imports RECORD-PRODUCTIONS
  imports K-SORT-LATTICE
  imports AUTO-CASTS
  imports AUTO-FOLLOW
endmodule
