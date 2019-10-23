// Copyright (c) 2015-2019 K Team. All Rights Reserved.

module KVAR-PROGRAM-PARSING
  imports BUILTIN-ID-TOKENS

  syntax KVar ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [prec(1), notInRules, token, autoReject]

              | #LowerId                                             [notInRules, token, autoReject]
              | #UpperId                                             [notInRules, token, autoReject]
endmodule

module KVAR-SYNTAX
  syntax KVar [token, hook(KVAR.KVar)]
endmodule

module KVAR
  imports KVAR-SYNTAX
  imports KVAR-SYMBOLIC
endmodule

module KVAR-SYMBOLIC [symbolic, kast]
  imports KVAR-SYNTAX
  imports STRING

  syntax KVar ::= String2KVar (String) [function, functional, hook(STRING.string2var)]
  syntax KVar ::= freshKVar(Int)    [freshGenerator, function, functional]
  syntax KItem  ::= "#parseToken"  "(" String "," String ")"  [function, klabel(#parseKVar), hook(STRING.parseToken)]
  rule String2KVar(S:String) => {#parseToken("KVar", S)}:>KVar
  rule freshKVar(I:Int) => String2KVar("_" +String Int2String(I))
endmodule

module SUBSTITUTION
  imports MAP
  imports KVAR

  syntax {Sort} Sort ::= Sort "[" KItem "/" KItem "]"  [function, hook(SUBSTITUTION.substOne), impure]
  syntax {Sort} Sort ::= Sort "[" Map "]"      [function, hook(SUBSTITUTION.substMany), impure]
endmodule
