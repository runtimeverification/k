module CINK-BASIC-SYNTAX
  syntax PrimType ::= "int" | "bool" | "void" 

  syntax Type ::= PrimType

  syntax Decl ::= Type Exps


  /*@ \subsection{Expressions} */


  syntax RVal ::= "cout" | "cin" | Bool | String | Int

  syntax Val ::= RVal

  syntax Exp ::= Id | Val
               | "(" Exp ")"  [bracket]
               | Exp "(" Exps ")" [strict(1), strictType(rvalue), result(RVal)]
| "++" Exp [strict]
| Exp "++" [strict]
               > left:
                 Exp "*" Exp [multiply, strict, strictType(rvalue), result(RVal)]
               | Exp "/" Exp [divide, strict, strictType(rvalue), result(RVal)]
               | Exp "%" Exp [latex({#1}\%{#2}), modulo, strict, strictType(rvalue), result(RVal)] 
               >  left:
                 Exp "+" Exp [plus, strict, strictType(rvalue), result(RVal)]
               | Exp "-" Exp [minus, strict, strictType(rvalue), result(RVal)]
               > left:
                 Exp "<" Exp  [lessthan, strict, strictType(rvalue), result(RVal)]
               | Exp ">" Exp  [greatthan, strict, strictType(rvalue), result(RVal)]
               | Exp "<=" Exp [latex({#1}\leq{#2}), lessequal, strict, strictType(rvalue), result(RVal)]
               | Exp "==" Exp [equality, strict, strictType(rvalue), result(RVal)]
               >
                 "!" Exp [strict, negation, strict, strictType(rvalue), result(RVal)] 
               > 
                 Exp "&&" Exp [left, strict(1), strictType(rvalue), result(RVal), latex({#1}\mathrel{\&\&}{#2}), conjunction]
               > 
                 Exp "||" Exp [left, strict(1), strictType(rvalue), result(RVal), disjunction]
               > left:
                 Exp "<<" Exp [left, seqstrict, strictType(rvalue), result(RVal), latex({#1}\mathrel{\tt <<}{#2}), write]
               | Exp ">>" Exp [left, latex({#1}\mathrel{\tt >>}{#2}), read]
               >
                 Exp "=" Exp [right, assign, strict(1)]
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
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1), strictType(rvalue), result(RVal)]
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
