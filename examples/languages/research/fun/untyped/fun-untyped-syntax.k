---------------------------------
--- FUN-UNTYPED-SYNTAX module ---
---------------------------------

--- TO DO: Change kmod ... endkm with module ... end module when the reported bug is fixed
kmod FUN-SYNTAX

/*@ \section{Syntax}
As explained above, FUN is an expression language, so every language construct
ends up being an expression construct (directly or indirectly).  We also allow
lists over identifiers and over expressions, like in most of our other languages,
which make FUN more user friendly.  Finally, as seen below, we define a syntax
which is more permissive that it should (that is, the builtin parser of our tool
may parse even incorrect programs as terms of sort \texttt{Exp}).  If one does
not like that, then one can use an external parser or one can define a type
checker/inferences (see fun/type-inference).  Note, however, that there is no
way one can define a grammar that parses precisely the well-typed FUN programs,
simply because those programs do not form a context-free language (the
simply-typed $\lambda$-calculus well-typed expressions already do not form a
context-free language).  */

/*@ The first group of expression constructs are the same as those of the SIMPLE
language, so we do not discuss them anymore here. */

  syntax Exp ::= Int | Bool
               | Id
               | Exp + Exp                [strict prec 33 gather(E e)]
               | Exp - Exp                [strict prec 33 gather(E e)]
               | Exp * Exp                [strict prec 31 gather(E e)]
               | Exp / Exp                [strict prec 31 gather(E e)]
               | Exp % Exp                [strict prec 31 gather(E e)]
               | - Exp                    [strict]
               | Exp < Exp                [strict prec 37]
               | Exp <= Exp               [strict prec 37]
               | Exp > Exp                [strict prec 37]
               | Exp >= Exp               [strict prec 37]
               | Exp == Exp               [strict prec 37]
               | Exp != Exp               [strict prec 37]
               | Exp and Exp              [strict prec 55 gather(E e)]
               | Exp or Exp               [strict prec 59 gather(E e)]
               | not Exp                  [strict prec 53]

/*@ The next group defines the usual functional constructs, namely function
abstraction, function application, let and letrec binders, and conditional.

*/
  syntax Exp ::= fun List{Exp} -> Exp
               | Exp List{Exp}      [strict prec 10 gather(E e)]
               | List{Exp} = List{Exp}    [prec 53]   --- Bindings
               | let Exp in Exp
               | letrec Exp in Exp
               | if Exp then Exp else Exp [strict(1)]

               | [ ]
               | [ List{Exp} ]            [strict hybrid prec 0]
               | car Exp                  [strict prec 0]
               | cdr Exp                  [strict prec 0]
               | null? Exp                [strict prec 0]
               | cons Exp Exp             [strict]

               | ref Exp                  [strict]
               | & Id
               | * Exp                    [strict]
               | Exp := Exp               [strict]
               | Exp ; Exp                [seqstrict prec 110 gather(e E)]

               | callcc Exp               [strict]

-----------------------------------------------------------------------------
--- Lists should be eventually builtin; for now, they need to be declared ---
-----------------------------------------------------------------------------
--- List{Id}
  syntax List{Id} ::= Id
                    | ( )
                    | List{Id} , List{Id} [strict hybrid assoc id: `(`) prec 70]

--- List{Exp}
  syntax List{Exp} ::= Exp | List{Id} | List{Exp} , List{Exp} [ditto]
-----------------------------------------------------------------------------
endkm


module FUN-DESUGARED-SYNTAX
  imports FUN-SYNTAX
  macro fun E1:Exp E2:Exp -> E:Exp = fun E1 -> fun E2 -> E
  macro (E1 El:List{Exp} = E2) = (E1 = fun El -> E2)
  macro (Xl1:List{Id} = El1:List{Exp}) and (Xl2:List{Id} = El2:List{Exp}) = ((Xl1,Xl2) = (El1,El2))
  macro [] = [()]
end module
