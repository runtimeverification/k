

kmod LANG-SYNTAX is including #INT + #ID
--- The main syntactic categories: Program, Class, Decl, Method, Exp and Stmt

--- Basic constructs for expressions
  syntax Exp ::= #Bool | Int | Id


-----------------------------------------------------------------------------
--- Lists
-----------------------------------------------------------------------------
--- List{Id}


  syntax Ids ::= List{Id,","} 

  syntax Exps ::= List{Exp,","}

  syntax Exp ::= Id ( Exps )


-----------------------------------------------------------------------------
endkm


kmod LANG-SEMANTICS is including LANG-SYNTAX + K + #CONVERSION

 configuration
    <T>
      <k>.K</k>
    </T>


endkm


kmod ISSUE039 is including LANG-SEMANTICS
 syntax Id ::= a | b | c
 syntax Exp ::= test
 macro test = a(b,c)

endkm
