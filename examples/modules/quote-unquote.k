kmod QUOTE-UNQUOTE is including K-VISITOR + PL-NAT
  syntax K ::= quote K
             | unquote K
             | lift K    [strict]
             | eval K    [strict]
             | mQuote( K , Nat ) [latex "{\it quote}({#1},{#2})"]

  macro mQuote(K,N) 
      = visit K applying quoteit[N]
               if label in SetItem(wklabel('quote_)) SetItem(wklabel('unquote_))

--- Code generation (via reflection)
  syntax KLabel ::= quoteit[ Nat ] [latex "{\it quote}_{\scriptsize{#1}}"]

  rule <k>quote K:K => mQuote(K,0) <_/k>
  rule quoteit[N](quote(K)) => visitedL('quote_)(mQuote(K,sNat(N))) 
  rule quoteit[0](unquote(K)) => K
  rule quoteit[sNat(N:Nat)](unquote(K)) => visitedL('unquote_)(mQuote(K,N))

  rule lift V:KResult => visitedK(V)
  rule eval visitedK(K) => K
endkm
