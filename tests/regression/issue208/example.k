kmod SKOOL-TYPED-SYNTAX is including #INT + #ID 

--- List{Id}
  syntax List{Id}  ::= Id | .List{Bottom} [latex "\kdot{\it List\{Bottom\}}"]

                     | List{Id} , List{Id}  [prec 70 assoc id: .List{Bottom} strict hybrid]

endkm



kmod ISSUE is
--------------------------------------------
--- SKOOL-TYPED-DYNAMIC-SEMANTICS module ---
--------------------------------------------

including SKOOL-TYPED-SYNTAX + K 

  syntax CellLabel ::= envStack       --- cell holding a stack, or List
  syntax ListItem ::= Id :: BagItem   --- Id is the class name, BagItem is its corresp. environment
  syntax K ::= lookupMember ( BagItem , Id )  --- BagItem is the envStack cell, Id is the member name
  syntax CellLabel ::= env 

  rule lookupMember(<envStack> _ :: <env> Env:Map </env>  => . <_/envStack>, X:Id)
    if notBool(X in keys(Env)) [structural]


endkm
