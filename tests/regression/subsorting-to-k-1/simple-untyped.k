------------------------------------
--- SIMPLE-UNTYPED-SYNTAX module ---
------------------------------------

module SIMPLE-UNTYPED
  syntax Exps ::= List{Exp,","} 
  syntax Exp ::= l-value ( Nat )
  syntax Exp ::= loc ( Nat )
  rule <k> l-value((L:Nat)) => loc(L) ...</k>
end module

