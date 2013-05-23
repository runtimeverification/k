module CINK-BASIC-SYNTAX
  syntax PrimType ::= "int" | "bool" | "void" 

  syntax Type ::= PrimType

  syntax Decl ::= Type Exps


  /*@ \subsection{Expressions} */


  syntax Val ::= "cout" | "cin" | Bool | String | Int

  syntax Exp ::= Id | Val
               | "(" Exp ")"  [bracket]
               | Exp "(" Exps ")" [strict(1)]
| "++" Exp
| Exp "++"
               > left:
                 Exp "*" Exp [multiply]
               | Exp "/" Exp [divide]
               | Exp "%" Exp [latex({#1}\%{#2}), modulo] 
               >  left:
                 Exp "+" Exp [plus]
               | Exp "-" Exp [minus]
               > left:
                 Exp "<" Exp  [lessthan]
               | Exp ">" Exp  [greatthan]
               | Exp "<=" Exp [latex({#1}\leq{#2}), lessequal]
               | Exp "==" Exp [equality]
               >
                 "!" Exp [strict, negation] 
               > 
                 Exp "&&" Exp [left, strict(1), latex({#1}\mathrel{\&\&}{#2}), conjunction]
               > 
                 Exp "||" Exp [left, strict(1), disjunction]
               > left:
                 Exp "<<" Exp [left, seqstrict, latex({#1}\mathrel{\tt <<}{#2}), write]
               | Exp ">>" Exp [left, latex({#1}\mathrel{\tt >>}{#2}), read]
               >
                 Exp "=" Exp [right, assign]
               >
                 "endl"

  /*@ \subsection{Statements} */

  syntax Stmt ::= Exp ";" [strict]
               | "#include" "<iostream>" 
               | "using" "namespace" "std" ";" 
                 [latex(\texttt{using namespace std;})]
               | Decl ";" [klabel(declStmt)]
               | "{" "}"
               | "{" Stmts "}"
               | "while" "(" Exp ")" Stmt 
               | "return" Exps ";" [strict]
               | Decl "(" Decls ")" "{" Stmts "}"
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1)]
               >
                 "if" "(" Exp ")" Stmt
  /*@
    A program is a sequence of statements:
  */
  syntax Pgm ::= Stmts 
  syntax Stmts ::= Stmt | Stmts Stmts [left]

  /* \subsection{Lists} */

  syntax Exps  ::= List{Exp,  ","} [strict]
  syntax Decls ::= List{Decl, ","}
 
endmodule
