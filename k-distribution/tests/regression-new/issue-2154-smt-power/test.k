requires "domains.md"

module TEST
    imports BOOL
    imports INT-SYMBOLIC

    syntax KItem ::= runLemma ( Bool ) | doneLemma ( Bool )
 // -------------------------------------------------------
    rule <k> runLemma(B) => doneLemma(B) ... </k>

    rule N ^Int N' <=Int M ^Int M' => true
      requires 0 <Int N andBool 0 <Int N'
       andBool 0 <Int M andBool 0 <Int M'
       andBool N <=Int M andBool N' <=Int M'
      [simplification, smt-lemma]
                     
endmodule
