---------------------------------
--- SKOOL-TYPED-SYNTAX module ---
---------------------------------

kmod SKOOL-TYPED-SYNTAX is 

--- Identifiers
--- Special identifiers for the class and method "main", and for the class "object"
  syntax #Id ::=  main
               | object

--- Types
  syntax Type ::= int 
                | bool 
                | void 
                | Type [ ] [prec 0]                                 --- array type
                | List{Type} -> Type [latex "{#1}\rightarrow{#2}"]  --- function type
                | #Id                                                --- class type

--- Typed identifiers
--- To be used as function parameters
  syntax VarType ::= Var : Type | Var : Type = Exp

--- Variables; we include arrays here as well, a[x][y][z]
  syntax Var ::= #Id
               | Var [ Exp ] [strict prec 1]

--- Declarations
--- There are three types of declarations, for variables, methods/constructors and classes
--- Variable declarations
  syntax VarDecl ::= var List{VarType} ; [prec 2]
--- Method/Constructor declarations
  syntax MethodDecl ::= method #Id ( ) : Type Stmt
                      | method #Id ( List{VarType} ) : Type Stmt
                      | method #Id ( ) Stmt
                      | method #Id ( List{VarType} ) Stmt
--- Class declarations
  syntax ClassDecl ::= class #Id { Stmts }
                     | class #Id extends #Id { Stmts }

--- Expressions
  syntax Exp ::= #Int | #Bool
               | Var
               | ++ Exp            [prec 0]                      --- want to increment o.f and a[5], too
               | Exp + Exp         [strict prec 33 gather(E e)]
               | Exp - Exp         [strict prec 33 gather(E e)]
               | Exp * Exp         [strict prec 31 gather(E e)]
               | Exp / Exp         [strict prec 31 gather(E e)]
               | Exp % Exp         [strict prec 31 gather(E e)]
               | - Exp             [strict]
               | Exp < Exp         [strict prec 37]
               | Exp <= Exp        [strict prec 37]
               | Exp > Exp         [strict prec 37]
               | Exp >= Exp        [strict prec 37]
               | Exp == Exp        [strict prec 37]
               | Exp != Exp        [strict prec 37]
               | Exp and Exp       [strict prec 55 gather(E e)]
               | Exp or Exp        [strict prec 59 gather(E e)]
               | not Exp           [strict prec 53]
               | Exp [ Exp ]       [ditto]
               | sizeOf ( Exp )    [strict]
               | Exp ( )
               | Exp ( List{Exp} ) [strict(2) prec 2]  --- unlike in SIMPLE, application is only strict(2)
               | read ( )

               | new #Id ( ) [prec 1]
               | new #Id ( List{Exp} ) [strict(2) prec 1]
               | this
               | super
               | Exp . #Id [prec 1]
               | Exp instanceOf #Id [strict(1) prec 0]  --- checking if object Exp is instance of class Id
               | cast Exp to Type  [strict(1) prec 0]  --- explicit casting


--- Statements
  syntax Stmt ::= { }
                | { Stmts }
                | Exp = Exp ;                [strict(2)]
                | Exp ;                      [strict]
                | if Exp then Stmt else Stmt [strict(1)]
                | if Exp then Stmt
                | while Exp do Stmt
                | for #Id = Exp to Exp do Stmt
                | return Exp ;               [strict]
                | write ( List{Exp} ) ;      [strict]  --- variadic

  syntax Stmts ::= VarDecl 
                 | MethodDecl
                 | ClassDecl
                 | Stmt
                 | Stmts Stmts               [prec 100 gather(e E)]


----------------------------------------------------------------------------
--- Lists should be eventually builtin; for now, they need to be declared ---
-----------------------------------------------------------------------------
--- List{Bottom}  (needed for consistencies)
--- do not add Bottom as subsort to anything else, like Id, Exp, etc
  syntax List{Bottom}  ::= Bottom | .List{Bottom} [latex "\kdot{\it List\{Bottom\}}"]
                     | List{Bottom} , List{Bottom} [prec 70 assoc id: .List{Bottom} strict hybrid] 
 
--- List{Type}
  syntax List{Type} ::= Type | List{Id} 
                     | List{Type} , List{Type} [ditto] 

--- List{Id}
  syntax List{Id}  ::= #Id | List{Bottom}
                     | List{Id} , List{Id} [ditto]

--- List{VarType}
  syntax List{VarType}  ::= VarType | List{Bottom}
                     | List{VarType} , List{VarType} [ditto]

--- List{Exp}
  syntax List{Exp} ::=  Exp | List{Id} 
                     | List{Exp} , List{Exp} [ditto]


--- List{Top}
  sort Top 
  syntax List{Top} ::= Top | List{Type} | List{VarType} | List{Exp} 
                     | List{Top} , List{Top} [ditto]

endkm


kmod SKOOL-TYPED-DYNAMIC-DESUGARED-SYNTAX is including SKOOL-TYPED-SYNTAX
-------------------------------------------------------------------------------
--- This module desugars some of SKOOL's language constructs into core ones ---
--- The idea is that we only want to give semantics to core constructs,     ---
--- so we get rid of the derived ones before we start the semantics         ---
-------------------------------------------------------------------------------
  macro var VT1:VarType, VT2:VarType, L:List{VarType} ; = var VT1 ; var VT2,L ;
  macro var V:Var : T:Type = E:Exp; = var V : T; V = E;
  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:#Id = E1:Exp to E2:Exp do S) = {var X : int ; X=E1; while X <= E2 do {S X=X+1;}}
  macro method F:#Id() : Tp:Type S = method F(.List{Bottom}) : Tp  S
  macro method F() S = method F() : F  S
  macro method F(L) S = method F(L) : F  S
  macro E() = E(.List{Bottom})
  macro O:Exp . F() = O . F(.List{Bottom}) 
  macro new C:#Id() = new C(.List{Bottom})
  macro class C {Ss:Stmts} = class C extends object {Ss}
endkm
