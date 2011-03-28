------------------------------------
--- SIMPLE-UNTYPED-SYNTAX module ---
------------------------------------

kmod SIMPLE-UNTYPED-SYNTAX is including PL-INT + PL-ID + K-LATEX

//@ \subsection*{Identifiers}
--- Special identifier for the function "main"
  syntax Id ::= main


//@ \subsection*{Declarations}
--- There are two types of declarations: for variables (including arrays) and for functions
  syntax Decl ::= var List{Exp} ;
                | function Id ( ) Stmt
                | function Id ( List{Id} ) Stmt

//@ \subsection*{Expressions}
  syntax Exp ::= Int | Bool | Id
               | ++ Exp             [prec 0]
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
               | Exp and Exp       [strict prec 39 gather(E e)]
               | Exp or Exp        [strict prec 39 gather(E e)]
               | not Exp           [strict prec 38]
               | Exp [ List{Exp} ] [strict prec 1] 
               | sizeOf ( Exp )    [strict]
               | Exp ( )
               | Exp ( List{Exp} ) [strict prec 2]
               | read ( )
               | Exp = Exp         [strict(2) prec 40  gather (e E)]

//@ \subsection*{Statements}
  syntax Stmt ::= { }
                | { Stmts }
                | Exp ;                      [strict prec 45]
                | if Exp then Stmt else Stmt [strict(1) prec 90]
                | if Exp then Stmt           [prec 89]
                | while Exp do Stmt          [prec 90]
                | for Id = Exp to Exp do Stmt[prec 90]
                | return Exp ;               [strict]
                | write ( Exp ) ;            [strict]
                | try Stmt catch ( Id ) Stmt [prec 90]
                | throw Exp ; [strict]
                | spawn Stmt [prec 90]
                | acquire Exp ;              [strict]
                | release Exp ;              [strict]
                | rendezvous Exp ;           [strict]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts               [prec 100 gather(e E)]


-----------------------------------------------------------------------------
/*@ \subsubsection*{Lists} should be eventually builtin; for now, they need to be declared  */
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

  macro var E,E':Exp,El:List{Exp}; = var E; var E',El;
  macro var X; = var X=0;
endkm
