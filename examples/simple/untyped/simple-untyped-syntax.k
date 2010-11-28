------------------------------------
--- SIMPLE-UNTYPED-SYNTAX module ---
------------------------------------

kmod SIMPLE-UNTYPED-SYNTAX is including PL-INT + PL-ID

--- Identifiers
--- Special identifier for the function "main"
  syntax Id ::= main

--- Variables; we include arrays here as well, a[x][y][z]
  syntax Var ::= Id
               | Var [ Exp ]       [strict prec 1]

--- Declarations
--- There are two types of declarations: for variables (including arrays) and for functions
  syntax Decl ::= var Var ;
                | function Id ( ) Stmt
                | function Id ( List{Id} ) Stmt

--- Expressions
  syntax Exp ::= Int | Bool
               | Var
               | ++ Id             [prec 0]
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
               | Exp ( List{Exp} ) [strict prec 2]
               | read ( )

--- Statements
  syntax Stmt ::= { }
                | { Stmts }
                | Exp = Exp ;                [strict(2)]
                | Exp ;                      [strict]
                | if Exp then Stmt else Stmt [strict(1)]
                | if Exp then Stmt
                | while Exp do Stmt
                | for Id = Exp to Exp do Stmt
                | return Exp ;               [strict]
                | write ( Exp ) ;            [strict]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts               [prec 100 gather(e E)]


-----------------------------------------------------------------------------
--- Lists should be eventually builtin; for now, they need to be declared ---
-----------------------------------------------------------------------------
--- List{Id}; the hybrid attribute says that a list of results becomes itself a result
  syntax List{Id} ::= Id
                    | .List{Id} [latex "\kdot{\it List\{Id\}}"]
                    | List{Id} , List{Id} [strict hybrid assoc id: .List{Id} prec 70]

--- List{Exp}
  syntax List{Exp} ::= Exp
                     | List{Id}
                     | List{Exp} , List{Exp} [ditto]
endkm


kmod SIMPLE-UNTYPED-DESUGARED-SYNTAX is including SIMPLE-UNTYPED-SYNTAX 
--------------------------------------------------------------------------------
--- This module desugars some of SIMPLE's language constructs into core ones ---
--- The idea is that we only want to give semantics to core constructs,      ---
--- so we get rid of the derived ones before we start the semantics          ---
--------------------------------------------------------------------------------
  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:Id = E1:Exp to E2:Exp do S) = {var X; X=E1; while X <= E2 do {S X=X+1;}}
  macro function F:Id() S = function F(.List{Id}) S
  macro E() = E(.List{Id})
endkm
