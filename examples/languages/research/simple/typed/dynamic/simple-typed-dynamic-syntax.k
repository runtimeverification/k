----------------------------------
--- SIMPLE-TYPED-SYNTAX module ---
----------------------------------

module SIMPLE-TYPED-SYNTAX 

//@ \section{Syntax}

//@ Function "main"
  syntax Id ::= main

/*@ \subsection{Types}
We declare here all the types that we will need for declarations: basic types, array types, and function types.
*/
  syntax Type ::= int | bool | void                                 
                | Type [ ] [prec 0]                               
                | List{Type} -> Type [latex "{#1}\rightarrow{#2}"] 

/*@ \subsection{Declarations}
 There are two types of declarations: for typed variables (including arrays) and for typed functions 
*/
  syntax Decl ::= var List{VarType} ;
                | function Id ( List{IdType} ) : Type Stmt
                | function Id ( ) : Type Stmt

/*@ Function parameter declarations now have to include types as well,
 so we define typed identifiers  and typed variables for that purpose
*/
  syntax IdType ::= Id : Type [prec 2]
  syntax VarType ::= IdType | Var : Type [ditto] 

/*@ Variables; we include arrays here as well, so that, e.g., a[x][y][z]
 can appear anywhere a variable can appear (declarations, lookup, assignment)
*/
  syntax Var ::= Id
               | Var [ List{Exp} ]       [strict prec 1]


//@\subsection{Expressions}
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
               | Exp [ List{Exp} ] [ditto]
               | sizeOf ( Exp )    [strict]
               | Exp ( )
               | Exp ( List{Exp} ) [strict prec 2]
               | read ( )
               | Exp = Exp         [strict(2) prec 40  gather (e E)]


  syntax Initializer ::= VarType = Exp  [ditto]
//@\subsection{Statements}
  syntax Stmt ::= { }
                | { Stmts }
                | Exp ;                       [strict prec 45]
                | if Exp then Stmt else Stmt  [strict(1) prec 90]
                | if Exp then Stmt            [prec 89]
                | while Exp do Stmt           [prec 90]
                | for Id = Exp to Exp do Stmt [prec 90]
                | return Exp ;                [strict]
                | write ( Exp ) ;             [strict]
                | try Stmt catch ( IdType ) Stmt  [prec 90]
                | throw Exp ;                 [strict]
                | spawn Stmt                  [prec 90]
                | acquire Exp ;               [strict]
                | release Exp ;               [strict]
                | rendezvous Exp ;            [strict]


  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts               [prec 100 gather(e E)]

/*@\subsection{Lists}
Lists should be eventually builtin; for now, they need to be declared 

 List{Bottom}  (needed for consistencies)

do not add Bottom as subsort to anything else, like Id, Exp, etc
*/
  sort Bottom
  syntax List{Bottom}  ::= Bottom | .List{Bottom} [latex "\kdot{\it List\{Bottom\}}"]
                     | List{Bottom} , List{Bottom} [prec 70 assoc id: .List{Bottom} strict hybrid]
 
--- List{Type}
  syntax List{Type} ::= Type | List{Bottom} 
                     | List{Type} , List{Type} [ditto] 
--- List{IdType}
  syntax List{IdType}  ::= IdType | List{Bottom}
                     | List{IdType} , List{IdType} [ditto]
--- List{VarType}
  syntax List{VarType} ::= VarType | Initializer |  List{IdType}
                     | List{VarType} , List{VarType} [ditto] 
--- List{Id}
  syntax List{Id}  ::= Id | List{Bottom}
                     | List{Id} , List{Id} [ditto]
--- List{Exp}
  syntax List{Exp} ::=  Exp | List{Id} 
                     | List{Exp} , List{Exp} [ditto]

  syntax List{Top} ::= List{VarType} | List{Exp} | List{Type}
                     | List{Top} , List{Top} [ditto]
end module


module SIMPLE-TYPED-DYNAMIC-DESUGARED-SYNTAX imports SIMPLE-TYPED-SYNTAX 
/*@\section{Desugared Syntax}
This module desugars some of SIMPLE's language constructs into core ones 
The idea is that we only want to give semantics to core constructs,      
so we get rid of the derived ones before we start the semantics          
*/

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:Id = E1:Exp to E2:Exp do S) = {var X : int ; X=E1; while X <= E2 do {S X=X+1;}}
  macro function F:Id() : Tp:Type S  = function F(.List{Bottom}) : Tp S
  macro E() = E(.List{Bottom})

  macro var VT:VarType, VT':VarType, VTL:List{VarType} ;
      = var VT:VarType ; var  VT':VarType, VTL:List{VarType} ;

  macro var V:Var : Tp = E ; = var V : Tp ; V = E ;
end module
