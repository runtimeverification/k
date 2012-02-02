
module EXP-TYPE-INFERENCE-SYNTAX

/*@ \section{Syntax}
Since the EXP type inferencer infers all the types automatically,
without requiring the user to declare any type explicitly, the EXP
syntax needed for the type inferencer is identical to the syntax used
for the dynamic, untyped semantics.  What we need is to change the
strictness of the conditional into strict in all its arguments
(indeed, all three of its arguments need to type), and to make sure
the \texttt{let} binder is not desugared anymore into $\lambda$
(because we want the type inferencer to be let-polymorphic).  Instead,
the \texttt{let} binder is declared to be strict in its second
argument (since the bound expression still needs to be typed). */

/*@ \subsection{Arithmetic constructs}
Identical to those in untyped EXP, including their \K annotations. */

  syntax Exp ::= #Int | #Bool | #Id
               | Exp "+" Exp                    [:strict prec 33 gather(E e):]
               | Exp "-" Exp                    [:strict prec 33 gather(E e):]
               | Exp "*" Exp                    [:strict prec 31 gather(E e):]
               | Exp "/" Exp                    [:strict prec 31 gather(E e):]
               | Exp "%" Exp                    [:strict prec 31 gather(E e):]
               | "-" Exp                        [:strict:]
               | Exp "<" Exp                    [:strict prec 37:]
               | Exp "<=" Exp                   [:strict prec 37:]
               | Exp ">" Exp                    [:strict prec 37:]
               | Exp ">=" Exp                   [:strict prec 37:]
               | Exp "==" Exp                   [:strict prec 37:]
               | Exp "!=" Exp                   [:strict prec 37:]
               | Exp "and" Exp                  [:strict prec 55 gather(E e):]
               | Exp "or" Exp                   [:strict prec 59 gather(E e):]
               | "not" Exp                      [:strict prec 53:]

/*@ \subsection{Functional constructs}
Syntactically identical to those in untyped EXP, although the \K
strictness of \texttt{let} changed to \texttt{strict(2)}.  Indeed,
since we do not desugar it anymore, we give it its own evaluation
strategy now. */

  syntax Exp ::= "lambda" #Id "." Exp           [:latex "\lambda{#1}.{#2}":]
               | Exp Exp                        [:strict prec 10 gather(E e):]
               | "if" Exp "then" Exp "else" Exp [:strict:]
               | "mu" #Id "." Exp               [:latex "\mu{#1}.{#2}":]
               | "let" #Id "=" Exp "in" Exp     [:strict(2):]
               | "letrec" #Id #Id "=" Exp in Exp

/*@ \subsection{Desugaring macros}
We only keep the desugaring of \texttt{letrec} into a \texttt{let}.
This way, \texttt{letrec} will also be polymorphic. */

  macro (letrec F:#Id X:#Id = E:Exp in E':Exp)
      = (let F = mu F . (lambda X . E) in E')

  syntax Exps ::= List{Exp,","}
//  syntax Exps ::= List{Exp,","}
end module


module TYPES
  imports EXP-TYPE-INFERENCE-SYNTAX
// This module should eventually be builtin and provided by the K
// framework tool.  Most type checkers/inferencers are expected to
// need it.  For now, we give it to the \K tool manually.
// Moreover, it needs to import EXP-TYPE-INFERENCE-SYNTAX
// (to have the entire list context in case you want to add
// List{Exp,","} later on; this is a current tool limitation).
// Please let us know if you'd like to have additional primitives here.

  syntax KResult ::= Type

// #Id should be added automatically as a subsort to K.
  syntax K ::= #Id

  syntax Type ::= "tv" #Nat             // type variables
                | Type "->" Type        // function type
  syntax Types ::= List{Type,","}

  syntax #Bool ::= "basicType" "(" Type ")"
                 | "typeVar" "(" Type ")"
  rule typeVar(T) => getKLabel(T) ==Bool 'tv_  [:structural:]

  syntax TypeSchema ::= Type
                      | "(" "forall" Types ")" Type
                          [:latex("(\forall{#1}){#2}"):]
  syntax TypeSchemas ::= List{TypeSchema,","}

  syntax Type ::= Type "+Type" #Nat [:latex("{#1}+_{\it Type}{#2}"):]
  rule tv(N:#Nat) +Type M:#Nat => tv(N +Nat M)  [:structural:]

// Free type variables.  These should be generic and builtin, for all binders.
  syntax Types ::= "ftv" "(" TypeSchemas ")"
  rule ftv(BT:Type) => .Types when basicType(BT)
  rule ftv(Tv:Type) => Tv,.Types when typeVar(Tv)
  rule ftv(T1:Type -> T2:Type) => union(ftv(T1),ftv(T2))
  rule ftv((forall Tvs:Types) T:Type) => diff(ftv(T),Tvs)
  rule ftv(.TypeSchemas) => .Types
  rule ftv(TS1:TypeSchema,TS2:TypeSchema,TSs:TypeSchemas)
    => union(ftv(TS1),ftv(TS2,TSs))

// The operations below should be generic and builtin, for all lists
  syntax Types ::= "union" "(" Types "," Types ")"
                 | "diff" "(" Types "," Types ")"
                     [:latex("{#1}-_{\it Types}{#2}"):]
                 | "insert" "(" Type "," Types ")"
                 | "delete" "(" Type "," Types ")"
  syntax #Nat ::= "|" Types "|"
  rule union(.Types,Ts':Types) => Ts'
  rule union((T,Ts:Types),Ts') => union(Ts,insert(T,Ts'))
  rule diff(Ts,.Types) => Ts
  rule diff(Ts,(T,Ts')) => diff(delete(T,Ts),Ts')
  rule insert(T,.Types) => T,.Types
  rule insert(T,(T',Ts)) => if T ==Bool T' then T',Ts else T',insert(T,Ts) fi
  rule delete(T,.Types) => .Types
  rule delete(T,(T',Ts)) => if T ==Bool T' then Ts else T',delete(T,Ts) fi
  rule |T,Ts| => 1 +Nat |Ts|
  rule |.Types| => 0

// This should be generalized and builtin: fresh name generator
  syntax Types ::= #Nat "from" Type
  rule 0 from tv(_:#Nat) => .Types
  rule (sNat N:#Nat) from tv(M:#Nat) => tv(M),(N from tv(sNat M))

// This could also be generic: subterm relation?
  syntax #Bool ::= Type "inType" Type [:latex("{#1}\in_{\it Type}{#2}"):]
  rule Tv inType BT  => false when typeVar(Tv) andBool basicType(BT)
  rule Tv inType Tv' => Tv ==Bool Tv' when typeVar(Tv) andBool typeVar(Tv')
  rule Tv inType (T1 -> T2) => (Tv inType T1) orBool (Tv inType T2)

// Type substitution: T[Ts / Tvs]* substitutes list of types Ts for
// list of type variables Tvs.  T[T' / Tv] substitutes type T' for type
// variable Tv in T.  These should also be generic and builtin.
  syntax Type ::= Type "[" Types "/" Types "]*"  [:prec(2):]
                | Type "[" Type  "/"  Type  "]"  [:prec(2):]  // auxiliary
  rule T[.Types / .Types]* => T
  rule T[T1,Ts:Types / Tv,Tvs]* => T[T1 / Tv][Ts / Tvs]*
  rule BT[T / Tv] => BT when basicType(BT) andBool typeVar(Tv)
  rule Tv':Type[T / Tv] => if Tv' ==Bool Tv then T else Tv' fi
    when typeVar(Tv')
  rule (T1 -> T2)[T / Tv] => T1[T / Tv] -> T2[T / Tv]

// Map application.  Should be generic and builtin.
  syntax Types ::= Map "[" Types "]*"  [:prec(1):]
  syntax Type  ::= Map "[" Type  "]"   [:prec(1):]

  rule .[T] => T
  rule (Tv |-> T':Type Theta:Map)[T] => Theta[T[T'/Tv]]

  rule Theta[.Types]* => .Types
  rule Theta[T,Ts:Types]* => Theta[T],Theta[Ts]*

// Next should probably be generic in some way, for all maps ...
// although note that it does something specific for type schemas.
// This was just a trick, to save us from defining map application on schemas
  syntax Types ::= "types" "(" Map ")"
  rule types(X:#Id |-> T TEnv:Map) => T,types(TEnv)
  rule types(X |-> (forall_)T TEnv) => T,types(TEnv)
  rule types(.Map) => .Types
end module


module EXP-TYPE-INFERENCE
  imports TYPES

/*@ Note that the module \texttt{TYPES} was included above.  This
module provides a series of primitive operations on types, such as
type variables, type schemas, free type variables and substitution,
etc.  We will discuss each of these on a by-need basis in the sequel. */

/*@ \section{Static Semantics}
We next define Milner's W type inference procedure as a static
semantics of EXP.  We use a (type) environment-based definition
and follow the same philosophy as in the static semantics of IMP, that
is, we iteratively rewrite fragments of the program into their types
until the entire program eventually rewrites to its type. */

/*@ \subsection{Extended syntax and results}
To do the above, we extend the syntax of expressions with types.
The imported module \texttt{TYPES} automatically subsorts
\texttt{Type} to \K results, so we do not need to do it here as well.
We do need, however, to declare our basic types.  The operation
\texttt{basicType} used below is provided by the \texttt{TYPES} module. */

  syntax Exp ::= Type
  syntax Type ::= "int" | "bool"        // basic types
  rule basicType(int) => true   [:structural:]
  rule basicType(bool) => true  [:structural:]

/*@ \subsection{Configuration}
Besides the \textsf{k} and \textsf{tenv} cells that are also present
in IMP's type checker, we now add two more top-level cells, one for
the unification procedure and one to hold the counter for fresh type
variables.  The cell \textsf{unification} holds a cell \textsf{eqns}
with equations that need to be solved, and a cell \textsf{mgu} which
holds the current most-general unifier. */

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <tenv color="LightSkyBlue"> .Map </tenv>
                  <unification color="black">
                    <eqns color="orange">
                      <eqn multiplicity="*" color="red"> .K </eqn>
                    </eqns>
                    <mgu color="blue"> .Map </mgu>
                  </unification>
                  <nextType> tv(0) </nextType>
                </T>

/*@ \subsection{Arithmetic expressions}
Primitive values rewrite to their types.  Arithmetic constructs, which
were all declared strict, generate type constraints for the types of
their arguments and return on the computation structure their result
type.  As seen in the unification section below, type equalities
posted on the computation structure are eventually collected and
solved by the unification procedure.  To save space and time, in the
rules below we match the \K labels corresponding to some of the
arithmetic constructs. */

  rule <k> I:#Int => int ...</k>
  rule <k> B:#Bool => bool ...</k>
  rule <k> X:#Id => T:Type ...</k> <tenv>... X |-> T ...</tenv>

  rule <k> L:KLabel(T1:Type,,T2:Type) => (T1,T2 = int,int) ~> int ...</k>
    when L ==Bool '_+_ orBool L ==Bool '_-_ orBool
       L ==Bool '_*_ orBool L ==Bool '_/_ orBool L ==Bool '_%_
  rule <k> - T => (T = int) ~> int ...</k>
  rule <k> L(T1,,T2) => (T1,T2 = int,int) ~> bool ...</k>
    when L ==Bool '_<_ orBool L ==Bool '_<=_ orBool L ==Bool '_>_ orBool
       L ==Bool '_>=_ orBool L ==Bool '_==_ orBool L ==Bool '_!=_
  rule <k> L(T1,,T2) => (T1,T2 = bool,bool) ~> bool ...</k>
    when L ==Bool '_and_ orBool L ==Bool '_or_

  rule <k> not T => (T = bool) ~> bool ...</k>
  rule <k> if T then T1 else T2 => (T,T1 = bool,T2) ~> T1 ...</k>

/*@ \subsection{Lambda}
We add a fresh type variable for the lambda-bound variable, then we
type the lambda-body, and then we construct the corresponding function
type.  At the same time, we recover the type environment. */

  syntax K ::= Type "->" "[]"
  rule <k> lambda X . E:Exp => E ~> (Tv -> []) ~> tenv(TEnv) ...</k>
          <tenv> TEnv:Map => TEnv[Tv/X] </tenv>
          <nextType> Tv:Type => Tv +Type 1 </nextType>
  rule T ~> (Tv -> []) => Tv -> T

// usual environment recovery
  syntax K ::= "tenv" "(" Map ")"
  rule <k> T ~> (tenv(TEnv) => .) ...</k> <tenv>  _ => TEnv </tenv>
    [:structural:]

/*@ \subsection{Application}
Once the two arguments of the application construct evaluate to types
\texttt{T1} and \texttt{T2}, we would like to say that \texttt{T1} is a
function type of the form \texttt{T2 -> Tr} and that the result of the
application is \texttt{Tr}.  However, since \texttt{T1} may not be a
function type yet, a simplistic rule of the form
``\texttt{(T2 -> Tr) T2 => Tr}'' will not always match.  To cover all
cases, we instead add a fresh type variable for the result type and
the type constraint that the first argument is a function type of the
right type, and finally we return the result type. */

  rule <k> T1 T2 => (T1 = (T2 -> Tv)) ~> Tv ...</k>
       <nextType> Tv => Tv +Type 1 </nextType>

/*@ \subsection{Mu}
We add a fresh type variable for the mu-bound variable and then we
enforce the my-body and the result type to be both equal to the type
of the mu-bound variable. */

  syntax K ::= Type "=" "[]"
  rule <k> mu X . E => E ~> (Tv = []) ~> Tv ~> tenv(TEnv) ...</k>
          <tenv> TEnv => TEnv[Tv / X] </tenv>
          <nextType> (Tv => Tv +Type 1) </nextType>
  rule T ~> (Tv = []) => Tv = T

/*@ \subsection{Let}
The trickiest part of Milner's W procedure is how to type the
\texttt{let} construct.  To allow for let-polymorphism, we bind the
variable to a {\em type schema} instead of a type.  A type schema can
be regarded as a type parametric, or universally quantified, in some
of its type variables.  Type schemas serve as skeletons for types.
Each time the let-bound variable is looked up in the environment, its
type schema is instantiated to a type by replacing its parameters with
fresh type variables.  This way, the let-bound variables can be used
multiple times in multiple contexts in the let-body, without
constraining its type more then needed.  The use of type schemas is
effectively equivalent to the following simpler but slower procedure:
first substitute the let-bound variable with its let-bound
expression within the let-body, and then type the resulting body.
The type schema therefore acts like a summary of the let-bound
expression typing effort, so that we do not redo that work at each
place where the let-bound variable is used.

There are two additional important observations regarding the first
rule below: first, we enforce that all type constraints are solved (by
requiring the \textsf{eqns} cell to be empty; then we apply the
resulting most-general unifier to the let-bound type; then we bind the
let variable to the type schema obtained by parametrizing the solved
let-bound type with all its context-free type variables, that is, by
all those type variables which do not appear in types bound to other
program variables in the type environment.  The type schema construct,
as well as the \texttt{ftv} (free type variables), difference and map
application operations, are defined in the imported \texttt{TYPES}
module. */

  rule <k> let X = T in E => E ~> tenv(TEnv) ...</k>
       <eqns> .Bag </eqns> <mgu> Theta:Map </mgu>
       <tenv> TEnv
        => TEnv[((forall diff(ftv(Theta[T]),ftv(Theta[types(TEnv)]*)))
                 Theta[T]) / X]
       </tenv>

  rule <k> X => T[|Tvs| from Tv / Tvs]* ...</k>
       <tenv>... X |-> (forall Tvs:Types) T ...</tenv>
       <nextType> Tv => Tv +Type | Tvs | </nextType>

/*@ \subsection{Final type}
When there is only one type left in the computation cell and all the
type constraints are solved, we apply the resulting mgu to that type
and that is the final result of the typing procedure.  We also remove
the unnecessary \textsf{eqns} cell, but prefer to keep the
\textsf{mgu} cell, as it may be insightful to see its contents in the
final configuration. */

// You can remove the <mgu\> cell, too, from the final configuration
  rule <k> T => Theta[T] </k> (<eqns> .Bag </eqns> => .) <mgu> Theta </mgu>


/*@ \section{Unification}
Unification can be defined quite elegantly in \K (and in AC rewriting,
in general): decompose and apply the equations until each of them has
the form $x = t$ where $x$ is a variable and $t$ is a term, thus
giving us the desired most general unifier; if $t$ contains $x$ in any
of the solved equations, then unification has failed.  For
optimization reasons, we prefer to separate the already calculated
most general unifier from the equations. */

  syntax K ::= Types "=" Types  [:strict prec(100):]

/*@ Type constraints are added to the set of equations as soon as they
are matched on the top of the computation.  Since the mgu is held
separately, we also apply it to the type equations.  This way, we are
guaranteed that the variables in the domain of the mgu will never
appear in the equations. */
  rule <k> Ts:Types = Ts':Types => . ...</k>
       (. => <eqn> Theta[Ts]* = Theta[Ts']* </eqn>)
       <mgu> Theta:Map </mgu>

//@ Cleanup, decomposition and orientation of equations.
  rule <eqn> Ts = Ts </eqn> => .

  rule <eqn> (T1,T2,Ts) = (T1':Type,T2':Type,Ts') </eqn>
    => <eqn> T1 = T1' </eqn> <eqn> (T2,Ts) = (T2',Ts') </eqn>

  rule <eqn> (T1 -> T2) = (T1' -> T2') </eqn>
    => <eqn> T1 = T1' </eqn> <eqn> T2 = T2' </eqn>

  rule <eqn> (T = Tv) => (Tv = T) </eqn>
    when typeVar(Tv) andBool notBool(typeVar(T))

/*@ When an equation contains a variable, it can be added as a binding
to the mgu.  While we know that the variables in the domain of the mgu
do not appear anywhere in the equations, it can be and usually is the
case that variables appearing in the equations also appear in the
codomain of the mgu.  Thus, we have to refine the mgu by applying the
new binding to all its terms.  Moreover, to maintain the equations
canonical in terms of the current mgu, we also have to refine the
remaining equations by applying the new mgu binding to them. */

  rule <eqns> Eqns:Bag <eqn> Tv = T </eqn> => refine(Eqns,Tv,T) </eqns>
       <mgu> Theta => Tv |-> T refine(Theta,Tv,T) </mgu>
    when notBool(Tv inType T)

  syntax Map ::= "refine" "(" Map "," Type "," Type ")"
  rule refine(.Map,_,_) => .Map
  rule refine(Tv':Type|->T':Type Theta, Tv, T)
    => Tv'|->T'[T/Tv] refine(Theta,Tv,T)

  syntax Bag ::= "refine" "(" Bag "," Type "," Type ")"
  rule refine(.Bag,Tv,T) => .Bag
  rule refine(<eqn> T1 = T2 </eqn> Eqns, Tv, T)
    => <eqn> T1[T/Tv] = T2[T/Tv] </eqn> refine(Eqns,Tv,T)

end module
