require "/modules/k-visitor.k"

module QUOTE-UNQUOTE-SYNTAX
  syntax Exp ::= "quote" Exp  [quote]
             | "unquote" Exp [unquote]
             | "lift" Exp    [lift, strict]
             | "eval" Exp    [eval, strict]
endmodule

module QUOTE-UNQUOTE 
  imports QUOTE-UNQUOTE-SYNTAX
  imports K-VISITOR
  syntax K ::= isQuote(K)  [function]
  rule isQuote(quote K) => true
  rule isQuote(unquote K) => true

  syntax K ::= mQuote(K, Int) [function, latex({\it quote}({#1},{#2}))]
  rule mQuote(K,N) 
    => visit K applying quoteit[N] if 'isQuote
    [structural]

// Code generation (via reflection)
  syntax KLabel ::= "quoteit" "[" Int "]" [latex({\it quote}_{\mbox{\scriptsize\ensuremath{#1}}})]

  rule <k>quote K:K => mQuote(K,0) ...</k>
  rule quoteit[N](quote(K)) => visitedL('quote_)(mQuote(K,N +Int 1)) 
  rule quoteit[0](unquote(K)) => K 
  rule quoteit[N](unquote(K)) => visitedL('unquote_)(mQuote(K,N -Int 1))  
    when (N >Int 0) 

  rule lift V:KResult => visitedK(V) 
  rule eval visitedK(K) => K 

  rule isVal(visitedK(_)) => true
endmodule
