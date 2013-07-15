module CINK-BASIC-SYNTAX 

  /*@ \subsection{Declarations}
    The declarations are used for declaring variables and function names
    together with their return types.
    We consider only integer and boolean variables. A return type of a function
    could be an integer, a boolean, or \texttt{void}.
  */

  syntax PrimType ::= "int" | "bool" | "void" 

  syntax Type ::= PrimType

  syntax Decl ::= Type Exps


  /*@ \subsection{Values} */

  /*@ The constants of the builtin types are primitive constructs and therefore
      they should be values.  
      \par
      In \Cpp the values are splitted in several categories:\\
\begin{quote}
-- An lvalue (so called, historically, because lvalues could appear on the 
left-hand side of an assignment expression) designates a function or an object.
[ Example: If E is an expression of pointer type, then
*E is an lvalue expression referring to the object or function to which E 
points. As another example, the result of calling a function whose return type
is an lvalue reference is an lvalue. --end example ]\\
-- An xvalue (an "eXpiring" value) also refers to an object, usually near
the end of its lifetime (so that its resources may be moved, for example). 
An xvalue is the result of certain kinds of expressions involving
rvalue references (8.3.2). [ Example: The result of calling a function whose 
return type is an rvalue reference is an xvalue. --end example ]\\
-- A glvalue ("generalized" lvalue) is an lvalue or an xvalue.\\
-- An rvalue (so called, historically, because rvalues could appear on the 
right-hand side of an assignment expression) is an xvalue, a temporary object 
(12.2) or subobject thereof, or a value that is not associated with an object.\\
-- A prvalue ("pure" rvalue) is an rvalue that is not an xvalue. 
[ Example: The result of calling a function whose return type is not a 
reference is a prvalue. The value of a literal such as 12, 7.3e5, or true is
also a prvalue. --end example ]
\end{quote}
      In order to keep the definition as sinple as possible, we consider only
      of these categories: \emph{lvalues} (\texttt{LVal}) and \emph{rvalues} 
      (\texttt{RVal}).
      The sort \texttt{Val} for values will be extended in the module describing
      the semantics.
      \par
      We prefer to declare \texttt{cin} and \texttt{cout} as values rather 
      than identifiers; the reason for this decision will be explained later.
   */

  syntax RVal ::= "cout" | "cin" | Bool | String | Int

  syntax Val ::= RVal | LVal

  /*@ \subsection{Expressions} */

  /*@
    We included in CinK a small subset of \Cpp language, the missing operators
    can be easily added in a similar way. Recall that the most important (from
    the semantic point of view) thing we have to mention for operators is the
    attribute \texttt{strict}, that specifies the evaluation order of the 
    operands. For instance, the arithmetic binary 
    operators are strict in both arguments, hence the behavior of some 
    programs could be undefined or non-determinsitic because the evaluation
    of the arguments could have side-effects.  The assignment operator is strict
    only in the second argument because the first argument must be evaluated 
    to an l-value. These features are common to many languages. In contrast
    to the other examples, the function call expression is strict only in the
    first argument (the function name) because the evaluation of the arguments
    it is depending on the bindding mechanism of the corresponding argument: 
    this can be call-by-value or call-by-reference. These two mechansims will
    be explained later. 
   */
  syntax Exp ::= Id | Val
               | "(" Exp ")"  [bracket]
               | Exp "(" Exps ")" [strict(1)]
               > left:
                 Exp "*" Exp [left, strict, multiply]
               | Exp "/" Exp [left, strict, divide]
               | Exp "%" Exp [left, strict, latex({#1}\%{#2}), modulo] 
               >  left:
                 Exp "+" Exp [left, strict, plus]
               | Exp "-" Exp [left, strict, minus]
               > left:
                 Exp "<" Exp  [left, strict, lessthan]
               | Exp ">" Exp  [left, strict, greatthan]
               | Exp "<=" Exp [left, strict, latex({#1}\leq{#2}), lessequal]
               | Exp "==" Exp [left, strict, equality]
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
                 Exp "=" Exp [right, strict(2), assign]
               >
                 "endl"

  /*@ \subsection{Statements}
    For now, we include in CinK only (a subset) of the imperative statements:
    expresion statement, bloc, sequential composition, while, and conditionals.
    We also added a minimal support for threads, similar to IMPPP, but using a
    \Cpp syntax and semantics.
   */

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

  /*@
    The above definitions are using lists of expressions and lists of 
    declarations, which are declared as follows:
  */
  syntax Exps  ::= List{Exp,  ","} [strict]
  syntax Decls ::= List{Decl, ","} [strict]
//  syntax Stmts ::= List{Stmt,""}

endmodule

