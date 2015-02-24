// Copyright (c) 2015 K Team. All Rights Reserved.

// Module defining only the sorts K and KString, useful for modularity
module BASIC-K
  syntax KItem
  syntax K
  syntax KString ::= r"[\\\"]([^\\\"\\n\\r\\\\]|[\\\\][nrtf\\\"\\\\])*[\\\"]"      [token, hook(org.kframework.kore.KString)]
    // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
  syntax KLabel
endmodule


module KAST
  imports BASIC-K
  syntax K     ::= KItem
  syntax KBott ::= "#token" "(" KString "," KString ")"  [klabel(#KToken), hook(org.kframework.kore.KToken)]
                 | "#klabel" "(" KLabel ")"              [klabel(#WrappedKLabel), hook(org.kframework.kore.meta.WrappedKLabel)]
                 | KLabel "(" KList ")"                  [klabel(#KApply), hook(org.kframework.kore.KApply)]

  syntax KLabel ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\s])+`" [token, hook(org.kframework.kore.KLabel)]
                  | r"[#a-z][a-zA-Z0-9]*"              [token, hook(org.kframework.kore.KLabel)]
                       // something that doesn't collide with meta-variables

  syntax KList ::= K
                 | ".::KList"           [klabel(#EmptyKList), hook(org.kframework.kore.EmptyKList)]
                 | KList "," KList      [klabel(#KList), left, assoc, unit(#EmptyKList), hook(org.kframework.kore.KList)]
endmodule


// To be used when parsing/pretty-printing ground configurations
module KSEQ
  imports KAST
  syntax KBott ::= ".::K"    [klabel(#EmptyK), hook(org.kframework.kore.EmptyK)]
                 | K "~>" K  [klabel(#KSequence), left, assoc, unit(#EmptyK), hook(org.kframework.kore.KSequence)]
  syntax left #KSequence
endmodule


// To be used when parsing/pretty-printing symbolic configurations
module KSEQ-SYMBOLIC
  imports KSEQ
  syntax KVariable ::= r"(?<![A-Za-z0-9\\_])(\\$|\\!|\\?)?([A-Z][A-Za-z0-9']*|_)"   [token, hook(org.kframework.kore.KVariable)]
  syntax KBott     ::= KVariable
  syntax KLabel    ::= KVariable
endmodule


// To be used to parse semantic rules
module K
  imports KSEQ-SYMBOLIC
  syntax KBott     ::= K "=>" K     [klabel(#KRewrite), hook(org.kframework.kore.KRewrite), non-assoc]
  syntax non-assoc #KRewrite
  syntax KBott     ::= "`" K "`"    [bracket]

endmodule
