in ../../../k-prelude


------------------------------------
--- SKOOL-UNTYPED-SYNTAX modules ---
------------------------------------

kmod SKOOL-UNTYPED-SORTS is including PL-INT + PL-ID
  sorts Var Exp Stmt Stmts

-----------------------------------------------------------------------------
--- Lists should be eventually builtin; for now, they need to be declared ---
-----------------------------------------------------------------------------
--- List{Id}
  syntax List{Id}  ::= 
                 Id 
               | .List{Id}
               | List{Id} , List{Id} [prec 70 assoc id: .List{Id}]

--- <SKOOL modified>
--- List{Var}
  syntax List{Var} ::=
                 Var 
               | List{Id} 
               | List{Var} , List{Var} [ditto]

--- List{Exp}
  syntax List{Exp} ::= 
                 Exp 
               | List{Var} 
               | List{Exp} , List{Exp} [ditto]
--- </SKOOL modified>
-----------------------------------------------------------------------------
endkm

kmod SKOOL-UNTYPED-EXPR is including SKOOL-UNTYPED-SORTS
  syntax Var ::= 
                 Id 
               | Exp [ Exp ] [prec 1 strict]
 
  syntax Exp  ::= 
                 Var | Int | Bool
               | ++ Id [prec 0]
               | Exp + Exp [gather(E e) prec 33 strict]
               | Exp - Exp [gather(E e) prec 33 strict]
               | Exp * Exp [gather(E e) prec 31 strict]
               | Exp / Exp [gather(E e) prec 31 strict]
               | Exp % Exp [gather(E e) prec 31 metadata "latex(renameTo _\\ensuremath\\%_)" strict]
               | - Exp [strict]
               | Exp < Exp [prec 37 metadata "latex(renameTo _\\ensuremath<_)" strict] 
               | Exp <= Exp [prec 37 metadata "latex(renameTo _\\ensuremath\\leq_)" strict] 
               | Exp > Exp [prec 37 metadata "latex(renameTo _\\ensuremath>_)" strict] 
               | Exp >= Exp [prec 37 metadata "latex(renameTo _\\ensuremath\\geq_)" strict] 
               | Exp == Exp [prec 37 strict] 
               | Exp != Exp [prec 37 strict] 
               | Exp and Exp [gather(E e) prec 55 strict] 
               | Exp or Exp  [gather(E e) prec 59 strict] 
               | not Exp [prec 53 strict]
               | sizeOf ( Exp ) [strict]
               | Exp ( )
               | Exp ( List{Exp} ) [prec 2 strict]
               | read ( )
             --- <SKOOL added>
               | new Id ( ) [prec 1]
               | new Id ( List{Exp} ) [prec 1 strict(2)]
               | this
               | Exp . Id ( ) [prec 1 strict(1)] 
               | Exp . Id ( List{Exp} ) [prec 1 strict(1 3)] 
               | super Id ( ) [prec 1]
               | super Id ( List{Exp} ) [prec 1 strict(2)]
               | Exp instanceOf Id [prec 0 strict(1)]
             --- </SKOOL added>
endkm

kmod SKOOL-UNTYPED-DECL is including SKOOL-UNTYPED-SORTS
  syntax VarDecl ::= 
                 var Var ; [prec 2] 

--- <SKOOL modified>
---                | function Id ( ) Stmt 
---                | function  Id ( List{Id} ) Stmt 
--- </SKOOL modified>

--- <SKOOL added>
  syntax MethodDecl ::=
                 method Id ( ) Stmt 
               | method Id ( List{Id} ) Stmt 

  syntax ClassDecl ::= 
                 class Id { Stmts }
               | class Id extends Id { Stmts }
--- </SKOOL added>
endkm

kmod SKOOL-UNTYPED-STMT is including SKOOL-UNTYPED-SORTS
  syntax Stmt ::=
                 { } [metadata "latex(renameTo \\{\\})"]
               | { Stmts } [gather(&) metadata "latex(renameTo \\{\_\\})"]
               | Exp = Exp ; [prec 2 strict(2)]
               | Exp ; [prec 50 strict]
               | if Exp then Stmt else Stmt [strict(1)]
               | if Exp then Stmt
               | while Exp do Stmt
               | for Id = Exp to Exp do Stmt
               | return Exp ; [strict]
               | write ( Exp ) ; [strict]
endkm

kmod SKOOL-UNTYPED-STMTS is including SKOOL-UNTYPED-DECL
  syntax Stmts ::= 
                 VarDecl 
             --- <SKOOL modified>
---                | function Id ( ) Stmt 
---                | function  Id ( List{Id} ) Stmt 
               | MethodDecl
               | ClassDecl
             --- </SKOOL modified>
               | Stmt
               | Stmts Stmts [prec 100 gather(e E)]
endkm


kmod SKOOL-UNTYPED-SYNTAX is
  including SKOOL-UNTYPED-EXPR + SKOOL-UNTYPED-STMT + SKOOL-UNTYPED-STMTS

  syntax Id ::= 
                 main 
             --- <SKOOL added>
               | object
             --- </SKOOL added>

endkm

---------------------------------------------
--- SKOOL-UNTYPED-DESUGARED-SYNTAX module ---
---------------------------------------------


kmod SKOOL-UNTYPED-DESUGARED-SYNTAX is including SKOOL-UNTYPED-SYNTAX 
--------------------------------------------------------------------------------
--- This module desugars some of SIMPLE's language constructs into core ones ---
--- The idea is that we only want to give semantics to core constructs,      ---
--- so we get rid of the derived ones before we start the semantics          ---
--------------------------------------------------------------------------------
  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:Id = E1:Exp to E2:Exp do S) = {var X; X=E1; while X <= E2 do {S X=X+1;}}
--- <SKOOL modified>
  macro method F:Id() S = method F(.List{Id}) S
--- </SKOOL modified>
  macro E() = E(.List{Id})

--- <SKOOL added>
  macro O:Exp . F() = O . F(.List{Id}) 
  macro new C:Id() = new C(.List{Id})
  macro O . F() = O . F(.List{Id})
  macro super F() = super F(.List{Id})

  macro class C {Ss:Stmts} = class C extends object {Ss}
--- </SKOOL added>
endkm

