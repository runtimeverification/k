// Copyright (c) 2015-2019 K Team. All Rights Reserved.

module KVAR-SYNTAX-PROGRAM-PARSING
  imports BUILTIN-ID-TOKENS

  syntax KVar ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [prec(1), token]

              | #LowerId                                             [token]
              | #UpperId                                             [token]
endmodule

module KVAR-SYNTAX
  syntax KVar [token, hook(KVAR.KVar)]
endmodule

module KVAR-COMMON
  imports KVAR-SYNTAX
  imports STRING

  syntax KVar ::= String2KVar (String) [function, functional, hook(STRING.string2token)]
  syntax KVar ::= freshKVar(Int)    [freshGenerator, function, functional]
endmodule

module KVAR-SYMBOLIC [symbolic, kast]
  imports KVAR-COMMON

  syntax KItem  ::= "#parseToken"  "(" String "," String ")"  [function, klabel(#parseKVar), hook(STRING.parseToken)]
  rule String2KVar(S:String) => {#parseToken("KVar", S)}:>KVar
endmodule

module KVAR
  imports KVAR-COMMON
  imports KVAR-SYMBOLIC

  rule freshKVar(I:Int) => String2KVar("_" +String Int2String(I))
endmodule

module SUBSTITUTION
  imports MAP
  imports KVAR

  syntax {Sort} Sort ::= Sort "[" KItem "/" KItem "]"  [function, hook(SUBSTITUTION.substOne), impure]
  syntax {Sort} Sort ::= Sort "[" Map "]"      [function, hook(SUBSTITUTION.substMany), impure]
endmodule
