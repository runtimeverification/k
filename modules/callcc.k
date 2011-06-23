require lambda

kmod CALLCC is including LAMBDA
  syntax K ::= callcc K [prec 50 strict]
  syntax KResult ::= cc ( K ) [latex "{\it cc}({#1})"]
  rule [save-cxt] : <k>(callcc(V:KResult) => (V cc(K:K))) ~> K</k> 
  rule [restore-cxt] : <k> (cc(K) V)~> _ => V ~> K</k> 
endkm
