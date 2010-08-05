load ml-prelude.maude

kmod IMP-SYNTAX is including ML-K 
  syntax Val    ::= Int++
  syntax NvExpType ::= int
  syntax Void   ::= void
  syntax ExpType   ::= Void | NvExpType | struct Id | & ExpType 
  syntax Struct ::= struct Id { Stmts } ; 

  syntax Var ::= Id | 
               | Exp -> Id

  syntax Exp ::= Var | Val 
               | `NULL
               | Exp + Exp [gather(E e) prec 33 strict]
               | Exp - Exp [gather(E e) prec 33 strict]
               | Exp * Exp [gather(E e) prec 31 strict]
               | Exp / Exp [gather(E e) prec 31 strict]
               | Exp % Exp [gather(E e) prec 31 metadata "latex(renameTo _\\ensuremath\\%_)" strict]
               | - Exp [prec 10 strict]
               | Exp < Exp [prec 35 metadata "latex(renameTo _\\ensuremath<_)" strict] 
               | Exp <= Exp [prec 35 metadata "latex(renameTo _\\ensuremath\\leq_)" strict] 
               | Exp > Exp [prec 35 metadata "latex(renameTo _\\ensuremath>_)" strict] 
               | Exp >= Exp [prec 35 metadata "latex(renameTo _\\ensuremath\\geq_)" strict] 
               | Exp == Exp [prec 35 strict] 
               | Exp != Exp [prec 35 strict] 
               | sizeOf ( Exp ) [strict]
               | Id ( )
               | Id ( List{Exp} ) [prec 2 strict(2)]
               | * Exp [prec 10 strict]
               | `! Exp [prec 5 strict ]
               | Exp && Exp [prec 55 gather(E e) strict(1) metadata "latex(renameTo _\\ensuremath{\\mathrel{\\&\\&}}_)"]
               | Exp || Exp [prec 57 gather(E e) strict(1) metadata "latex(renameTo _\\ensuremath\\parallel_)"]
               | Exp `? Exp : Exp [prec 59 strict(1)]
               | getReturnValue ExpType
               | new ExpType


  syntax Stmt ::= Decl | StmtAnnot
               | Exp = Exp ; [prec 60 strict(2)]
               | Exp ; [prec 65 strict]
               | if ( Exp ) Stmt else Stmt [prec 93 strict(1)]
               | if ( Exp ) Stmt [prec 95]
               | while ( Exp ) Stmt
               | for Id = Exp to Exp do Stmt
               | return Exp ; [strict]
               | return ;
               | { } [metadata "latex(renameTo \\{\\})"]
               | { Stmts } [gather(&) metadata "latex(renameTo \\{\_\\})"]
               | Stmts Stmts [prec 100 gather(e E)]
---               | alloc ( List{KLabel} ) [strict]   --- see "new" operator
---               | free ( Exp ) [strict]  --- see delete (below)
               | delete Exp ; [strict]
               | breakpoint ;
               | watch ;
               | functionEnd

  syntax Stmts ::= Decl | Stmt | StmtAnnot
                | Stmts Stmts [ditto]

  ---op __ : DeclAnnots DeclAnnots -> DeclAnnots [prec 100 gather(e E)]

  syntax Decl  ::= ExpType List{Exp} ; | Struct
---  syntax Decls ::= Decl
---                 | Decls Decls [ditto]

  syntax StmtAnnot  ::=
                        /*`assume Bag */   [prec 99 strat(0)]
                      | /*`assert Bag */   [prec 99 strat(0)]
                      | /*`invariant Bag */ [prec 99 strat(0)]

  syntax DeclAnnot  ::=  
                        /*`pre Bag */ /*`post Bag */ [prec 99 strat(0)]
                        | noAnnot

  syntax Decl ::= DeclAnnot
                      | ExpType Id ( ) DeclAnnot { Stmts }
                      | ExpType Id ( Stmts ) DeclAnnot { Stmts }
                      | ExpType Id ( ) { Stmts }
                      | ExpType Id ( Stmts ) { Stmts }
                      | void main ( ) { Stmts }

--- lists

  syntax List{Id} ::= Id | .List{Id}
                    | List{Id} ,,, List{Id} [assoc id: .List{Id}]


  syntax List{Val} ::= Val 
                    | List{Val} ,,, List{Val} [ditto]

  syntax List{Exp} ::= Exp | List{Id} | List{Val}
                    | List{Exp} ,,, List{Exp} [ditto]

---env
  op _|->[_:_] : Id  Val  ExpType -> MapItem
---struct
  op _|->_ : Id  List -> MapItem
  op [_:_+_] :  Id  ExpType  Int++ -> ListItem
---heap
  op emptySn : -> Id
  op @scalar :  -> Field
  op _._ : Id Id -> Field 
  op _|->_:[_:_] : Int++  Val Field  ExpType -> MapItem

endkm

kmod IMP-DESUGARED-SYNTAX is including IMP-SYNTAX
--------------------------------------------------------------------------------
--- This module desugars some of IMP's language constructs into core ones    ---
--- The idea is that we only want to give semantics to core constructs,      ---
--- so we get rid of the derived ones before we start the semantics          ---
--------------------------------------------------------------------------------

  macro NULL = 0
  macro E1:Exp != E2:Exp = !(E1 == E2)
  macro if (E:Exp) S:Stmt = if(E) S else {}

  syntax Stmts ::= noneStmts  --- empty sequence of statements
  macro __`(`)_`{_`}(T:ExpType, F:Id, DA:DeclAnnot, Ss:Stmts ) = __`(_`)_`{_`}(T, F, noneStmts, DA, Ss )
  macro __`(`)`{_`}(T, F, Ss ) = __`(_`)_`{_`}(T, F, noneStmts, noAnnot, Ss )
  macro __`(_`)`{_`}(T, F, Sss:Stmts, Ss ) = __`(_`)_`{_`}(T, F, Sss, noAnnot, Ss )
  macro _`(`)(F) = _`(_`)(F,.List{Id})

  macro __;(T, *F) = __;(&T, F)   
endkm
