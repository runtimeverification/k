---------------------------------
--- FUN-UNTYPED-SYNTAX module ---
---------------------------------

kmod FUN-SYNTAX is including PL-INT + PL-ID

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
               | fun List{Exp} -> Exp
               | List{Exp} List{Exp}      [strict prec 10 gather(E e)]
               | callcc Exp               [strict]
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

-----------------------------------------------------------------------------
--- Lists should be eventually builtin; for now, they need to be declared ---
-----------------------------------------------------------------------------
--- List{Id}
  syntax List{Id} ::= Id
                    | ( )
                    | List{Id} , List{Id} [strict hybrid assoc id:() prec 70]

--- List{Exp}
  syntax List{Exp} ::= Exp | List{Id} | List{Exp} , List{Exp} [ditto]
-----------------------------------------------------------------------------
endkm


kmod FUN-DESUGARED-SYNTAX is including FUN-SYNTAX
  macro fun E1:Exp E2:Exp -> E:Exp = fun E1 -> fun E2 -> E
  macro (E1 El:List{Exp} = E2) = (E1 = fun El -> E2)
  macro (Xl1:List{Id} = El1:List{Exp}) and (Xl2:List{Id} = El2:List{Exp}) = ((Xl1,Xl2) = (El1,El2))
  macro [] = [()]
endkm
