/*!
\title{KOOL --- Typed --- Dynamic}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@
\section{Abstract}
This is the \K dynamic semantics of the typed KOOL language.  It is
very similar to the semantics of the untyped KOOL, the difference
being that we now check the typing policy dynamically.  Since we have
to now declare the types of variables and methods, we adopt a syntax
for those which is closed to that of Java.  Like in the semantics of
untyped KOOL, where we borrowed almost all the semantics of untyped
SIMPLE, we are going to also borrow much of the semantics of
dynamically typed SIMPLE here.  We will highlight the differences
between the dynamically typed and the untyped KOOL as we proceed with
the semantics. */

module KOOL-TYPED-DYNAMIC-SYNTAX

/*@ \section{Syntax}
Like for the untyped KOOL language, the syntax of typed KOOL extends
that of typed SIMPLE with object-oriented constructs.
 */

/*@ \subsection{Syntax from SIMPLE}
The syntax below is taken ad litteram from dynamically typed SIMPLE.
Like in untyped KOOL, we removed from the \K annotated syntax of
SIMPLE the construct for function declarations (because we want to
call them methods now) and the one for function application (because
application is not strict in the first argument anymore due to dynamic
method dispatch).  Moreover, we removed the syntax of \texttt{try-catch}
from that of SIMPLE, because we want to have typed exceptions in KOOL. */

/*@ \subsection{KOOL Additional Syntax}
The KOOL syntactic extensions below are almost identical to their
untyped variants in untyped KOOL.  The only difference is that we add
a new type construct for class types and that now methods take typed
arguments (we achieved this the same way as in typed SIMPLE) and can
also have an explicit return type.  As a convenience to the
programmer, a macro adds an explicit type \texttt{void} whenever a
return type is not provided (e.g., one may not want to write a return
type for constructors in KOOL typed programs).  The syntax of typed
exceptions differs from that of typed SIMPLE in that the variable
bound by \texttt{catch} is now expected to be typed (we use
\textit{Exp}, but we only give semantics for the case when it has the
form \textit{Id:Type}. */

  syntax Id ::= "Object" | "Main"

//@ \subsection{Types}

  syntax Type ::= "void" | "int" | "bool" | "string"
                | Id                              // KOOL class
                | Type "[" "]"
                > Types "->" Type
                | "(" Type ")"           [bracket]
  syntax Types ::= List{Type,","}

//@ \subsection{Declarations}

  syntax Param ::= Type Id
  syntax Params ::= List{Param,","}

  syntax Decl ::= Type Exps ";"
                | Type Id "(" Params ")" Block    // stays like in typed SIMPLE
                | "class" Id Block                // KOOL
                | "class" Id "extends" Id Block   // KOOL    

//@ \subsection{Expressions}

  syntax Exp ::= Int | Bool | String | Id
               | "this"                                 // KOOL
               | "super"                                // KOOL
               | "(" Exp ")"             [bracket]
               | "++" Exp
               | Exp "instanceOf" Id     [strict(1)]    // KOOL
               | "(" Id ")" Exp          [strict(1)]    // KOOL  cast
               | "new" Id "(" Exps ")"   [strict(2)]    // KOOL
               | Exp "." Id                             // KOOL
               > Exp "[" Exps "]"        [strict]
               > Exp "(" Exps ")"        [strict(2)]    // was strict in SIMPLE
               | "-" Exp                 [strict]
               | "sizeOf" "(" Exp ")"    [strict]
               | "read" "(" ")"
               > left:
                 Exp "*" Exp             [strict, left]
               | Exp "/" Exp             [strict, left]
               | Exp "%" Exp             [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "!" Exp                 [strict]
               > left:
                 Exp "&&" Exp            [strict(1), left]
               | Exp "||" Exp            [strict(1), left]
               > "spawn" Block
               > Exp "=" Exp             [strict(2), right]

  syntax Exps ::= List{Exp,","}

//@ \subsection{Statements}

  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
                | "for" "(" Stmt Exp ";" Exp ")" Block
                | "print" "(" Exps ")" ";"              [strict]
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "try" Block "catch" "(" Param ")" Block
                | "throw" Exp ";"                       [strict]
                | "join" Exp ";"                        [strict]
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Stmt
                 | Stmts Stmts                          [right]

//@ \subsection{Desugaring macros}
  rule if (E) S => if (E) S else {}                                     [macro]
  rule for(Start Cond; Step) {S:Stmts} => {Start while(Cond){S Step;}}  [macro]
  rule T:Type E1:Exp, E2:Exp, Es:Exps; => T E1; T E2, Es;               [macro]
  rule T:Type X:Id = E; => T X; X = E;                                  [macro]

  rule class C:Id S => class C extends Object S                     // KOOL

endmodule


module KOOL-TYPED-DYNAMIC
  imports KOOL-TYPED-DYNAMIC-SYNTAX


endmodule
