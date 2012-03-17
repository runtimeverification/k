require k-visitor

module QUOTE-UNQUOTE imports K-VISITOR
  syntax K ::= "quote" K
             | "unquote" K
             | "lift" K    [strict]
             | "eval" K    [strict]

  declare isQuote : K -> K
  define isQuote(quote K) => true
  define isQuote(unquote K) => true

  declare mQuote : K #Nat -> K [latex "{\it quote}({#1},{#2})"]
  define mQuote(K,N) 
    => visit K applying quoteit[N] if 'isQuote
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
