module CINK-SYNTAX is
  including #INT +  #ID

  /*@ \subsubsection*{Expressions.} */
  syntax Decl ::= "int" Exp [prec 40] | "void" Id [prec 40]  
  syntax Exp ::= Int | Id
               | Exp "+" Exp [:gather (E e) prec 33 strict:]
               | Exp "-" Exp [:gather (E e) prec 33 strict:]
               | Exp "*" Exp [:gather (E e) prec 31 strict:]
               | Exp ">" Exp [:prec 37 strict:] 
               | Exp "=" Exp [:strict(2) prec 40 gather (e E):]
               | "printf" "(" \"%d;\" , Exp ")" [:strict:] 
               | "scanf(\"%d\", &" Id ")"
               | Id "(" Exps ")" [:prec 0 strict(2):]
//               | Id "(" ")" [:prec 0:]
               | Decl

  syntax Id ::= "main"

  /*@ \subsubsection*{Statements.} */
  syntax Stmt ::= Exp ; [:prec 45 strict:]
//               | "{" "}"
               | "{" Stmts "}"
               | "if" "(" Exp ")" Stmt [:prec 47:]
               | "if" "(" Exp ")" Stmt "else" Stmt [:prec 46 strict(1):]
               | "while" "(" Exp ")" Stmt 
               | "return" Exp ";"
               | Decl "(" Decls ")" "{" Stmts "}"
               | Decl "(" ")" "{" Stmts "}"
               | "#include" "<stdio.h>" 


  /*@ \subsubsection*{Programs.} */
  syntax Pgm ::= Stmts 

  /*@ \subsubsection*{Lists.} */
  syntax Stmts ::= List{Stmt,""}
  syntax Ids ::= List{Id,","}
  syntax Decls ::= List{Decl, ","}
  syntax Exps ::= List{Exp, ","}
end module

kmod CINK-DESUGARED-SYNTAX is including CINK-SYNTAX 
/*@
  Some statements or expression are syntactic sugars.
  Their semantics is given by desugaring.
*/

  macro if(E:Exp) St:Stmt = if(E) St else {}
//  macro I:Id () = I (.Bottom)
// macro _`(`)`{_`}(Decl:Decl, Stmts:Stmts) = Decl (.Bottom) { Stmts }
//  macro void X:Id = int X
//  macro (int X = E ;) = int X ; X = E ;
endkm

module ISSUE is including CINK-SYNTAX

  syntax Val ::= Int | "void" 
  syntax Exp ::= Val 
  syntax  Vals ::= List{Val, ","} 

end module

