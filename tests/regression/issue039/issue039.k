

module LANG-SYNTAX 
--- The main syntactic categories: Program, Class, Decl, Method, Exp and Stmt

--- Basic constructs for expressions
  syntax Exp ::= Bool | Int | Id


-----------------------------------------------------------------------------
--- Lists
-----------------------------------------------------------------------------
--- List{Id}


  syntax Ids ::= List{Id,","} 

  syntax Exps ::= List{Exp,","}

  syntax Exp ::= Id ( Exps )


-----------------------------------------------------------------------------
end module


module LANG-SEMANTICS imports LANG-SYNTAX 

 configuration
    <T>
      <k>.K</k>
    </T>


end module


module ISSUE039 imports LANG-SEMANTICS
 syntax Id ::= a | b | c
 syntax Exp ::= test
 macro test = a(b,c)

end module
