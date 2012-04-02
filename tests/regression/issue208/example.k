kmod SKOOL-TYPED-SYNTAX is 

--- List{Id}
  syntax Ids  ::= List{Id,","} [prec 70]

endkm



kmod ISSUE is
--------------------------------------------
--- SKOOL-TYPED-DYNAMIC-SEMANTICS module ---
--------------------------------------------

including SKOOL-TYPED-SYNTAX 

  syntax CellLabel ::= envStack       --- cell holding a stack, or List
  syntax ListItem ::= Id :: BagItem   --- Id is the class name, BagItem is its corresp. environment
  syntax K ::= lookupMember ( BagItem , Id )  --- BagItem is the envStack cell, Id is the member name
  syntax CellLabel ::= env 

  rule lookupMember(<envStack> _:Id :: <env> Env:Map </env>  => . <_/envStack>, X:Id)
    when notBool(X in keys(Env)) [structural]


endkm
