require "/modules/k-visitor.k"

module QUOTE-UNQUOTE-SYNTAX
  syntax K ::= "quote" K
             | "unquote" K
             | "lift" K    [strict]
             | "eval" K    [strict]
endmodule

module QUOTE-UNQUOTE 
  imports QUOTE-UNQUOTE-SYNTAX
  imports K-VISITOR
  syntax K ::= "isQuote" "(" K ")"  [klabel(isQuote)]
  rule isQuote(quote K) => true [anywhere]
  rule isQuote(unquote K) => true [anywhere]

  syntax K ::= "mQuote" "(" K "," Nat ")" [klabel(mQuote), latex("{\it quote}({#1},{#2})")]
  rule mQuote(K,N) 
    => visit K applying quoteit[N] if 'isQuote
    [structural, anywhere]

// Code generation (via reflection)
  syntax KLabel ::= "quoteit" "[" Nat "]" [latex("{\it quote}_{\mbox{\scriptsize\ensuremath{#1}}}")]

  rule <k>quote K:K => mQuote(K,0) ...</k>
  rule quoteit[N](quote(K)) => visitedL('quote_)(mQuote(K,N +Int 1)) 
  rule quoteit[0](unquote(K)) => K 
  rule quoteit[N:Nat](unquote(K)) => visitedL('unquote_)(mQuote(K,N -Int 1))  
    when (N >Int 0) 

  rule lift V:KResult => visitedK(V) 
  rule eval visitedK(K) => K 
endmodule
