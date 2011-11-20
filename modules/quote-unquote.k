require k-visitor

module QUOTE-UNQUOTE imports K-VISITOR
  syntax K ::= "quote" K
             | "unquote" K
             | "lift" K    [strict]
             | "eval" K    [strict]
             | "mQuote" "(" K "," #Nat ")" [latex "{\it quote}({#1},{#2})"]
  syntax KLabel ::= "isQuote"

  rule isQuote(quote K) => true
  rule isQuote(unquote K) => true

  rule mQuote(K,N) 
    => visit K applying quoteit[N] if isQuote
    [structural]

--- Code generation (via reflection)
  syntax KLabel ::= "quoteit" "[" #Nat "]" [latex "{\it quote}_{\mbox{\scriptsize\ensuremath{#1}}}"]

  rule <k>quote K:K => mQuote(K,0) <_/k>
  rule quoteit[N](quote(K)) => visitedL('quote_)(mQuote(K,sNat(N))) 
  rule quoteit[0](unquote(K)) => K
  rule quoteit[sNat(N:#Nat)](unquote(K)) => visitedL('unquote_)(mQuote(K,N))

  rule lift V:KResult => visitedK(V)
  rule eval visitedK(K) => K
end module
