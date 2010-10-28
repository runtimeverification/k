----------------------------------
--- SIMPLE-TYPED-SYNTAX module ---
----------------------------------

kmod SIMPLE-TYPED-SYNTAX is including PL-INT + PL-ID 

--- Variables; we include arrays here as well, so that, e.g., a[x][y][z]
--- can appear anywhere a variable can appear (declarations, lookup, assignment)
  syntax Var ::= Id
               | Var [ Exp ] [prec 1 strict]

--- Expressions
  syntax Exp ::= Var | Int | Bool
               | ++ Id [prec 0]
               | Exp + Exp [gather(E e) prec 33 strict]
               | Exp - Exp [gather(E e) prec 33 strict]
               | Exp * Exp [gather(E e) prec 31 strict]
               | Exp / Exp [gather(E e) prec 31 strict]
               | Exp % Exp [gather(E e) prec 31 latex "{#1}\%{#2}" strict]
               | - Exp [strict]
               | Exp < Exp [prec 37 latex "{#1}<{#2}" strict]
               | Exp <= Exp [prec 37 latex "{#1}\leq{#2}" strict]
               | Exp > Exp [prec 37 latex "{#1}>{#2}" strict]
               | Exp >= Exp [prec 37 latex "{#1}\geq{#2}" strict]
               | Exp == Exp [prec 37 strict]
               | Exp != Exp [prec 37 strict]
               | Exp and Exp [gather(E e) prec 55 strict]
               | Exp or Exp  [gather(E e) prec 59 strict]
               | not Exp [prec 53 strict]
               | Exp [ Exp ] [ditto]
               | sizeOf ( Exp ) [strict]
               | Exp ( )
               | Exp ( List{Exp} ) [prec 2 strict]
               | read ( )

--- Types; we declare here all the types that we will need for declarations
  syntax Type ::= int | bool | void                                 --- basic types
                | Type [ ] [prec 0]                                 --- array types
                | List{Type} -> Type [latex "{#1}\rightarrow{#2}"]  --- function types

--- Function parameter declarations now have to include types as well,
--- so we define typed identifiers for that purpose
  syntax IdType ::= Id : Type

--- Declarations
  syntax Decl ::= var Var : Type ; [prec 2]
                | function Id ( ) : Type Stmt
                | function Id ( List{IdType} ) : Type Stmt

--- Statements
  syntax Stmt ::= { }
                | { Stmts } [gather(&)]
                | Exp = Exp ; [prec 2 strict(2)]
                | Exp ; [prec 50 strict]
                | if Exp then Stmt else Stmt [strict(1)]
                | if Exp then Stmt
                | while Exp do Stmt
                | for Id = Exp to Exp do Stmt
                | return Exp ; [strict]
                | write ( Exp ) ; [strict]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts [prec 100 gather(e E)]

--- Function "main"
  syntax Id ::= main


-----------------------------------------------------------------------------
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
--- List{IdType}
  syntax List{IdType}  ::= IdType | List{Bottom}
                     | List{IdType} , List{IdType} [ditto]
--- List{Id}
  syntax List{Id}  ::= Id | List{Bottom}
                     | List{Id} , List{Id} [ditto]
--- List{Exp}
  syntax List{Exp} ::=  Exp | List{Id} 
                     | List{Exp} , List{Exp} [ditto]
endkm


kmod SIMPLE-TYPED-DYNAMIC-DESUGARED-SYNTAX is including SIMPLE-TYPED-SYNTAX 
--------------------------------------------------------------------------------
--- This module desugars some of SIMPLE's language constructs into core ones ---
--- The idea is that we only want to give semantics to core constructs,      ---
--- so we get rid of the derived ones before we start the semantics          ---
--------------------------------------------------------------------------------
  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:Id = E1:Exp to E2:Exp do S) = {var X : int ; X=E1; while X <= E2 do {S X=X+1;}}
  macro function F:Id() : Tp:Type S  = function F(.List{Bottom}) : Tp S
  macro E() = E(.List{Bottom})
endkm
