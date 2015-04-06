// Copyright (c) 2015 K Team. All Rights Reserved.

// Module defining only the sorts K and KString, useful for modularity
module BASIC-K
  syntax K
  syntax KString ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fa-f]{2})|([\\\\][u][0-9a-fa-f]{4})|([\\\\][u][0-9a-fa-f]{8}))*[\\\"]"      [token, hook(org.kframework.kore.KString)]
    // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
  syntax KLabel
endmodule


module KAST
  imports BASIC-K
  syntax KItem
  syntax K     ::= KItem
  syntax KBott ::= "#token" "(" KString "," KString ")"  [klabel(#KToken), hook(org.kframework.kore.KToken)]
                 | "#klabel" "(" KLabel ")"              [klabel(#WrappedKLabel), hook(org.kframework.kore.meta.WrappedKLabel)]
                 | KLabel "(" KList ")"                  [klabel(#KApply), hook(org.kframework.kore.KApply)]
  syntax KTop ::= KItem
  syntax KItem ::= KBott

  syntax KLabel ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\s])+`" [token, hook(org.kframework.kore.KLabel)]
                  | r"[#a-z][a-zA-Z0-9]*"              [token, hook(org.kframework.kore.KLabel), autoReject]
                       // something that doesn't collide with meta-variables

  syntax KList ::= K
                 | r"\\.(::)?KList"           [klabel(#EmptyKList), hook(org.kframework.kore.EmptyKList)]
                 | KList r",,?" KList   [klabel(#KList), left, assoc, unit(#EmptyKList), hook(org.kframework.kore.KList), prefer]
endmodule


// To be used when parsing/pretty-printing ground configurations
module KSEQ
  imports KAST
  syntax KBott ::= r"\\.(::)?K"    [klabel(#EmptyK), hook(org.kframework.kore.EmptyK)]
                 | K "~>" K  [klabel(#KSequence), left, assoc, unit(#EmptyK), hook(org.kframework.kore.KSequence)]
  syntax left #KSequence
  syntax KBott     ::= "`" K "`"    [bracket]
endmodule


// To be used when parsing/pretty-printing symbolic configurations
module KSEQ-SYMBOLIC
  imports KSEQ
  syntax KVariable ::= r"(?<![A-Za-z0-9\\_])(\\$|\\!|\\?)?([A-Z][A-Za-z0-9']*|_)"   [token, autoReject, hook(org.kframework.kore.KVariable)]
  syntax KBott     ::= KVariable
  syntax KLabel    ::= KVariable
endmodule

module KCELLS
  imports KAST

  syntax Cell
  syntax Bag ::= Bag Bag  [left, assoc, klabel(#cells), unit(#EmptyBag)]
               | r"\\.(::)?Bag" [klabel(#EmptyBag)]
               | Cell
  syntax K ::= Bag
  syntax Bag ::= KBott
endmodule

module RULE-CELLS
  imports KCELLS
  // if this module is imported, the parser automatically
  // generates, for all productions that have the attribute 'cell' or 'maincell',
  // a production like below:
  //syntax Cell ::= "<top>" #OptionalDots K #OptionalDots "</top>" [klabel(<top>)]

  syntax #OptionalDots ::= "..." [klabel(#dots)]
                         | ""    [klabel(#noDots)]
endmodule

module CONFIG-CELLS
  imports KCELLS
  syntax #CellName ::= r"[a-zA-Z0-9\\-]+"  [token]
  syntax Cell ::= "<" #CellName #CellProperties ">" K "</" #CellName ">" [klabel(#configCell)]
  syntax #CellProperties ::= #CellProperty #CellProperties [klabel(#cellPropertyList)]
                           | ""                            [klabel(#cellPropertyListTerminator)]
  syntax #CellProperty ::= #CellName "=" KString    [klabel(#cellProperty)]

endmodule


module REQUIRES-ENSURES
  imports BASIC-K

  syntax RuleContent ::= K                                 [klabel("#ruleNoConditions")]
                       | K r"(requires)|(when)" K                    [klabel("#ruleRequires")]
                       | K "ensures"  K                    [klabel("#ruleEnsures")]
                       | K r"(requires)|(when)" K "ensures" K        [klabel("#ruleRequiresEnsures")]
endmodule

module CAST-AUTO-GEN
  // if this module is imported, the parser automatically
  // generates, for all sorts, productions of the form:
  // Sort ::= KBott
  // K ::= Sort
  // Sort ::= Sort "::Sort"
  // Sort ::= Sort ":Sort"
  // K    ::= Sort "<:Sort"
  // Sort ::= K    ":>Sort"
  // this is part of the mechanism that allows concrete user syntax in K
endmodule

// To be used to parse semantic rules
module K
  imports KSEQ-SYMBOLIC
  imports REQUIRES-ENSURES
  imports CAST-AUTO-GEN
  syntax KBott     ::= K "=>" K     [klabel(#KRewrite), hook(org.kframework.kore.KRewrite), non-assoc]
  syntax non-assoc #KRewrite
  syntax KBott     ::= "HOLE"         [klabel([])]

endmodule
