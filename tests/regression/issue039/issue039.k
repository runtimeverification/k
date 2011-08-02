

kmod LANG-SYNTAX is including #INT + #ID
--- The main syntactic categories: Program, Class, Decl, Method, Exp and Stmt

--- Basic constructs for expressions
  syntax Exp ::= #Bool | #Int | #Id


-----------------------------------------------------------------------------
--- Lists
-----------------------------------------------------------------------------
--- List{Id}


  syntax List{Id} ::= #Id | List{Id} , List{Id} [prec 70 assoc]

  syntax List{Exp} ::= Exp | List{Id} | List{Exp} , List{Exp} [ditto]

  syntax Exp ::= #Id ( List{Exp} )


-----------------------------------------------------------------------------
endkm


kmod LANG-SEMANTICS is including LANG-SYNTAX + K + #CONVERSION

  syntax K ::= List{Exp} 

 configuration
    <T>
      <k>.K</k>
    </T>


endkm


kmod ISSUE039 is including LANG-SEMANTICS
 syntax #Id ::= a | b | c
 syntax Exp ::= test
 macro test = a(b,c)

endkm
