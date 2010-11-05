---in ../../../../k-prelude

kmod SKOOL-TYPED-SYNTAX is including PL-INT + PL-ID 

  sorts Var Exp Decl Stmt Stmts
---<SKOOL added>
  syntax Id ::=
                 main
               | object 
---               | Id [ ] [prec 0]

---</SKOOL added>

  syntax Type ::= int 
                | bool 
                | void 
                | Type [ ] [prec 0]
                | Id [ ] [prec 0]
                | List{Type} -> Type [metadata "latex(renameTo _\\ensuremath\\rightarrow_)"]
                ---<SKOOL added>
                | class Id    --- for classes
                ---</SKOOL added>

  syntax IdType ::= Id : Type
                  | Id : Id

--- variable names
  syntax Var ::= Id 
               | Var [ Exp ] [prec 1 strict]

--- expressions
  syntax Exp ::=   Var | Int | Bool         
                | ++ Id [prec 0 strict]
                | Exp + Exp [gather(E e) prec 33 strict]
                | Exp - Exp [gather(E e) prec 33 strict]
                | Exp * Exp [gather(E e) prec 31 strict]
                | Exp / Exp [gather(E e) prec 31 strict]
                | Exp % Exp [gather(E e) prec 31 strict]
                |  - Exp [strict]
                | Exp < Exp [prec 37 metadata "latex(renameTo _\\ensuremath<_)" strict] 
                | Exp <= Exp [prec 37 metadata "latex(renameTo _\\ensuremath\\leq_)" strict] 
                | Exp > Exp [prec 37 metadata "latex(renameTo _\\ensuremath>_)" strict] 
                | Exp >= Exp [prec 37 metadata "latex(renameTo _\\ensuremath\\geq_)" strict] 
                | Exp == Exp [prec 37 strict] 
                | Exp != Exp [prec 37 strict] 
                | Exp and Exp [gather(E e) prec 55 strict] 
                | Exp or Exp  [gather(E e) prec 59 strict] 
                | not Exp [prec 53 strict]
                | Exp [ Exp ] [ditto] 
                | sizeOf ( Exp ) [strict]
                | Exp ( ) [strict]
                | Exp ( List{Exp} ) [prec 2 strict]
                | read ( )
             --- <SKOOL added>
               | new Id ( ) [prec 1]
               | new Id ( List{Exp} ) [prec 1 strict(2)]
               | this
               | super
               | Exp . Id [prec 1 strict(1)] 
               | Exp instanceOf Id [prec 0 strict(1)]
             --- </SKOOL added>

--- declarations
  syntax VarDecl ::=
                | var Var : Type ; [prec 2] 
                | var Var : Id ; [prec 2] 
--- <SKOOL modified>
---                | function Id ( ) : Type Stmt 
---                | function  Id ( List{IdType} ) : Type Stmt 

  syntax MethodDecl ::=
                 method Id ( ) : Type Stmt 
               | method Id ( List{IdType} ) : Type Stmt 
               | method Id ( ) : Id Stmt 
               | method Id ( List{IdType} ) : Id Stmt 
               | method Id ( ) Stmt 
               | method Id ( List{IdType} ) Stmt 
       

  syntax ClassDecl ::= 
                 class Id { Stmts }
               | class Id extends Id { Stmts }
--- </SKOOL modified>

--- instructions
  syntax Stmt ::= 
                  { } [metadata "latex(renameTo \\{\\})"]
                | { Stmts } [gather(&) metadata "latex(renameTo \\{\_\\})" strict]
                | Exp = Exp ; [prec 2 strict(2)]
                | Exp ; [prec 50 strict]
                | if Exp then Stmt else Stmt [strict]
                | if Exp then Stmt
                | while Exp do Stmt [strict]
                | for Id = Exp to Exp do Stmt
                | return Exp ; [strict]
                | write ( Exp ) ; [strict]

--- statements
  syntax Stmts ::=
                 VarDecl 
             --- <SKOOL modified>
---               Decl 
               | MethodDecl
               | ClassDecl
             --- </SKOOL modified>
               | Stmt
               | Stmts Stmts [prec 100 gather(e E) seqstrict]

----------------------------------------------------------------------------
--- Lists should be eventually builtin; for now, they need to be declared ---
-----------------------------------------------------------------------------
--- List{Bottom}  (needed for consistencies)
--- do not add Bottom as subsort to anything else, like Id, Exp, etc
  sort Bottom 
  syntax List{Bottom}  ::= Bottom | .List{Bottom}
                     | List{Bottom} , List{Bottom} [prec 70 assoc id: .List{Bottom} strict hybrid] 
 
--- List{Type}
  syntax List{Type} ::= Type | List{Bottom} 
                     | List{Type} , List{Type} [ditto] 

--- List{Id}
  syntax List{Id}  ::= Id | List{Bottom}
                     | List{Id} , List{Id} [ditto]

--- List{IdType}
  syntax List{IdType}  ::= IdType | List{Bottom}
                     | List{IdType} , List{IdType} [ditto]

--- List{Exp}
  syntax List{Exp} ::=  Exp | List{Id} 
                     | List{Exp} , List{Exp} [ditto]


--- List{Top}
  sort Top 
  syntax List{Top} ::= Top | List{Type} | List{IdType} | List{Exp} 
                     | List{Top} , List{Top} [ditto]

endkm


kmod SKOOL-TYPED-STATIC-DESUGARED-SYNTAX is including SKOOL-TYPED-SYNTAX 
--------------------------------------------------------------------------------
--- This module desugars some of SKOOL's language constructs into core ones ---
--- The idea is that we only want to give semantics to core constructs,      ---
--- so we get rid of the derived ones before we start the semantics          ---
--------------------------------------------------------------------------------
  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:Id = E1:Exp to E2:Exp do S) = {var X : int ; X=E1; while X <= E2 do {S X=X+1;}}
--- <SKOOL modified>
---  macro function F:Id() : Tp:Type S  = function F(.List{Bottom}) : Tp S
---  macro E() = E(.List{Bottom})

--- resolving class ids
  macro var F : F' ; = var F : class F' ;
  macro F : F' = F : class F'
  macro F[] = (class F)[]
  macro method F:Id() : F':Id S =  method F:Id() : class F':Id S 
  macro method F:Id(L:List{IdType}) : F':Id  S 
      = method F:Id(L:List{IdType}) : class F'  S 


  macro method F:Id() : Tp:Type S = method F(.List{Bottom}) : Tp  S
  macro method F:Id() S = method F() : F  S
  macro method F:Id(L:List{IdType}) S = method F(L) : class F  S
--- </SKOOL modified>
  macro E() = E(.List{Bottom})

--- <SKOOL added>
  macro O:Exp . F() = O . F(.List{Bottom}) 
  macro new C:Id() = new C(.List{Bottom})

  macro class C {Ss:Stmts} = class C extends object {Ss}
--- </SKOOL added>
endkm


