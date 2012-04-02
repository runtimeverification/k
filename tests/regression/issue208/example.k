module SKOOL-TYPED-SYNTAX

--- List{Id}
  syntax Ids  ::= List{Id,","} [prec 70]

end module



module ISSUE
--------------------------------------------
--- SKOOL-TYPED-DYNAMIC-SEMANTICS module ---
--------------------------------------------

imports SKOOL-TYPED-SYNTAX 

  syntax CellLabel ::= "envStack"       --- cell holding a stack, or List
  syntax ListItem ::= Id "::" BagItem   --- Id is the class name, BagItem is its corresp. environment
  declare lookupMember : BagItem Id -> K  --- BagItem is the envStack cell, Id is the member name
  syntax CellLabel ::= "env" 

  define lookupMember(<envStack> _:Id :: <env> Env:Map </env>  => . <_/envStack>, X:Id)
    when notBool(X in keys(Env))


end module
