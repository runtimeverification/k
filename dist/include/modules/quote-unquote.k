require "k-visitor.k"

module QUOTE-UNQUOTE imports K-VISITOR
  syntax K ::= "quote" K
             | "unquote" K
             | "lift" K    [strict]
             | "eval" K    [strict]

  syntax K ::= "isQuote" "(" K ")"  [function,klabel(isQuote)]
  rule isQuote(quote K) => true [function, anywhere]
  rule isQuote(unquote K) => true [function, anywhere]

  syntax K ::= "mQuote" "(" K "," Int ")" [function, klabel(mQuote), latex("{\it quote}({#1},{#2})")]
  rule mQuote(K,N) [function, anywhere]
    => visit K applying quoteit[N] if 'isQuote
    [structural]

  //Code generation (via reflection)
  syntax KLabel ::= "quoteit" "[" Nat "]" [latex("{\it quote}_{\mbox{\scriptsize\ensuremath{#1}}}")]

  rule <k>quote K:K => mQuote(K,0) ...</k>
  rule quoteit[N](quote(K)) => visitedL('quote_)(mQuote(K,N +Int 1)) 
  rule quoteit[0](unquote(K)) => K 
  rule quoteit[N:Nat](unquote(K)) => visitedL('unquote_)(mQuote(K,N -Int 1))  
    when (N >Int 0) 

  rule lift V:KResult => visitedK(V) 
  rule eval visitedK(K) => K 
endmodule
