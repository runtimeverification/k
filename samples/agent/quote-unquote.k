// Copyright @ 2012-2014.  K Team.  All Rights Reserved.

require "/modules/k-visitor.k"

module QUOTE-UNQUOTE-SYNTAX
  syntax Exp ::= "quote" Exp    [quote]
               | "unquote" Exp  [unquote]
               | "lift" Exp     [lift, strict]
               | "eval" Exp     [eval, strict]
endmodule

module QUOTE-UNQUOTE
  imports QUOTE-UNQUOTE-SYNTAX
  imports K-VISITOR

  syntax Bool ::= isQuoted(Exp)     [function]
  rule isQuoted(quote E) => true
  rule isQuoted(unquote K) => true

// Quotes code starting with a certain quoting depth
  syntax Exp ::= mQuote(Exp, Int)   [function]
// Uses the pre-defined visitor
  rule mQuote(E, N) => #visit(E,, #visitor('quoteit(N),, #label('isQuoted)))

// Code generation (via reflection)
  syntax Exp ::= quoteit(Int,Exp)
  rule quote E => mQuote(E, 0)
  rule quoteit(N, quote E)   => #visiting.kapp(#label('quote_),,   mQuote(E, N +Int 1))
  rule quoteit(0, unquote E) => E
  rule quoteit(N, unquote E) => #visiting.kapp(#label('unquote_),, mQuote(E, N -Int 1))
  when (N >Int 0)

  rule lift V:Val => #visited(V)
  rule eval #visited(E) => E

  rule isVal(#visited(_)) => true
endmodule
