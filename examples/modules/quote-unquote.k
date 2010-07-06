kmod QUOTE-UNQUOTE is including K-VISITOR + PL-NAT
  syntax K ::= quote K
             | unquote K
             | lift K    [strict]
             | eval K    [strict]

--- Code generation (via reflection)
  syntax KLabel ::= quoteit[ Nat ] [latex "{\it quote}_{\scriptsize{#1}}"]

  rule <k>quote K:K 
       => visit K applying quoteit[0]
                  if label in SetItem(wklabel('quote_)) SetItem(wklabel('unquote_)) <_/k>
  rule quoteit[N](quote(K)) => visitedL('quote_)(visit K applying quoteit[sNat(N)]
                  if label in SetItem(wklabel('quote_)) SetItem(wklabel('unquote_)))
  rule quoteit[0](unquote(K)) => K
  rule quoteit[sNat(N:Nat)](unquote(K)) 
    => visitedL('unquote_)(visit K applying quoteit[N]
                  if label in SetItem(wklabel('quote_)) SetItem(wklabel('unquote_)))

  rule lift V:KResult => visitedK(V)
  rule eval visitedK(K) => K
endkm
