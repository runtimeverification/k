require "modules/unification.k"

/*!
\setlength{\parindent}{1em}
\title{EXP --- Static Semantics --- W Type Inferencer}
\author{Grigore Ro\c{s}u and
        Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
	(\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@
\section{Abstract}
This is the \K definition of the classic W type inference procedure
for the EXP language.  The EXP language and W were originally proposed
by Robin Milner in his seminal paper on type inference below:
\begin{quote}
Robin Milner. A theory of type polymorphism in programming.
{\em Journal of Computer and System Sciences}, 17(3):348-375, 1978.
\end{quote}
See the \K definition of untyped EXP for the semantics of the various
EXP language constructs.
*/

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



/*@ \subsection{Functional constructs}
Syntactically identical to those in untyped EXP, although the \K
strictness of \texttt{let} changed to \texttt{strict(2)}.  Indeed,
since we do not desugar it anymore, we give it its own evaluation
strategy now. */

  syntax Exp ::= "(" Exp ")"               [bracket]
               | Exp Exp                    [left,strict]
	       > left: Int | Bool | Id
               | Exp "+" Exp		    [strict]
               | Exp "-" Exp                [strict]
               > left: Exp "*" Exp         [strict]
               | Exp "/" Exp                [strict]
               | Exp "%" Exp                [strict]
               | "-" Exp                    [strict]
               > non-assoc: Exp "<" Exp      [strict]
               | Exp "<=" Exp               [strict]
               | Exp ">" Exp                [strict]
               | Exp ">=" Exp               [strict]
               | Exp "==" Exp               [strict]
               | Exp "!=" Exp               [strict]
               > right: Exp "and" Exp       [strict]
               | Exp "or" Exp               [strict]
               | "not" Exp                  [strict]
               > left: 
                 "if" Exp "then" Exp "else" Exp [strict]
               > left: "let" Id "=" Exp "in" Exp [strict(2)]
               | "letrec" Id Id "=" Exp "in" Exp
               > left: "mu" Id "." Exp           [latex(\mu{#1}.{#2})]
               | "lambda" Id "." Exp       [latex(\lambda{#1}.{#2})]
               

/*@ \subsection{Desugaring macros}
We only keep the desugaring of \texttt{letrec} into a \texttt{let}.
This way, \texttt{letrec} will also be polymorphic. */

  rule (letrec F:Id X:Id = E:Exp in E':Exp)
    => (let F = mu F . (lambda X . E) in E') [macro, anywhere]

//  syntax Exps ::= List{Exp,","}
endmodule


module TYPES
  imports EXP-TYPE-INFERENCE-SYNTAX
  imports UNIFICATION
// This module should eventually be builtin and provided by the K
// framework tool.  Most type checkers/inferencers are expected to
// need it.  For now, we give it to the \K tool manually.
// Moreover, it needs to import EXP-TYPE-INFERENCE-SYNTAX
// (to have the entire list context in case you want to add
// List{Exp,","} later on; this is a current tool limitation).
// Please let us know if you'd like to have additional primitives here.

  syntax KResult ::= Type

  syntax TypeVar ::= UnificationVar

  syntax Type ::= TypeVar             // type variables
                | BasicType
                | Type "->" Type  [strict]      // function type
  syntax Types ::= List{Type,","}

  syntax TypeSchema ::= Type
                      | "(" "forall" Types ")" Type
                          [latex((\forall{#1}){#2})]
  syntax TypeSchemas ::= List{TypeSchema,","}

// Free type variables.  These should be generic and builtin, for all binders.
  syntax Types ::= "ftv" "(" TypeSchemas ")"
  rule ftv(BT:BasicType) => .Types [anywhere]
  rule ftv(Tv:TypeVar) => Tv,.Types [anywhere]
  rule ftv(T1:Type -> T2:Type) => union(ftv(T1),ftv(T2)) [anywhere]
  rule ftv((forall Tvs:Types) T:Type) => diff(ftv(T),Tvs) [anywhere]
  rule ftv(.TypeSchemas) => .Types [anywhere]
  rule ftv(TS1:TypeSchema,TS2:TypeSchema,TSs:TypeSchemas)
    => union(ftv(TS1),ftv(TS2,TSs)) [anywhere]

// The operations below should be generic and builtin, for all lists
  syntax Types ::= "union" "(" Types "," Types ")"
                 | "diff" "(" Types "," Types ")"
                     [latex({#1}-_{\it Types}{#2})]
                 | "insert" "(" Type "," Types ")"
                 | "delete" "(" Type "," Types ")"
  syntax Nat ::= "|" Types "|"
  rule union(.Types,Ts':Types) => Ts' [anywhere]
  rule union((T:Type,Ts:Types),Ts':Types) => union(Ts,insert(T,Ts')) [anywhere]
  rule diff(Ts:Types,.Types) => Ts [anywhere]
  rule diff(Ts:Types,(T:Type,Ts':Types)) => diff(delete(T,Ts),Ts') [anywhere]
  rule insert(T:Type,.Types) => T,.Types [anywhere]
  rule insert(T:Type,(T':Type,Ts:Types)) => #if T ==K T' #then T',Ts #else T',insert(T,Ts) #fi [anywhere]
  rule delete(T:Type,.Types) => .Types [anywhere]
  rule delete(T:Type,(T':Type,Ts:Types)) => #if T ==K T' #then Ts #else T',delete(T,Ts) #fi [anywhere]
  rule |T:Type,Ts:Types| => 1 +Int |Ts| [anywhere]
  rule |.Types| => 0 [anywhere]

// This should be generalized and builtin: fresh name generator
  syntax Types ::= "freshVars" "(" Int "," Int ")"
  rule freshVars(_:Int,0) => .Types [anywhere]
  rule freshVars(M:Int, N:Int) => freshVar(M),freshVars(M +Int 1, N -Int 1) 
    when N >Int 0
    [anywhere]

// Type substitution: T[Ts / Tvs]* substitutes list of types Ts for
// list of type variables Tvs.  
  syntax Type  ::= Type "[" Types "/" Types "]*"  
  rule T:Type[.Types / .Types]* => T [anywhere]
  rule T:Type[T1:Type,Ts:Types / Tv:Type,Tvs:Types]* => applySubst(subst(eqn(Tv,,T1)),T)[Ts / Tvs]* [anywhere]


// Next should probably be generic in some way, for all maps ...
// although note that it does something specific for type schemas.
// This was just a trick, to save us from defining map application on schemas
  syntax Types ::= "types" "(" Map ")"
  rule types(X:Id |-> T:Type TEnv:Map) => T,types(TEnv) [anywhere]
  rule types(X:Id |-> (forall_)T:Type TEnv:Map) => T,types(TEnv) [anywhere]
  rule types(.Map) => .Types [anywhere]
endmodule


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
  syntax BasicType ::= "int" | "bool"        // basic types

/*@ \subsection{Configuration}
Besides the \textsf{k} and \textsf{tenv} cells that are also present
in IMP's type checker, we now add two more top-level cells, one for
the unification procedure and one to hold the counter for fresh type
variables.  The top cell holds a cell \textsf{mgu} which
holds the current most-general unifier. */

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Exp </k>
                  <tenv color="LightSkyBlue"> .Map </tenv>
                  <mgu color="blue"> subst(.List{K}) </mgu>
                  <nextVar> 0 </nextVar>
                </T>
                <resultType multiplicity="?"> .K </resultType>
				
/*@ \subsection{Arithmetic expressions}
Primitive values rewrite to their types.  Arithmetic constructs, which
were all declared strict, generate type constraints for the types of
their arguments and return on the computation structure their result
type.  Type equalities
posted on the computation structure are eventually collected and
solved by the unification procedure.  To save space and time, in the
rules below we match the \K labels corresponding to some of the
arithmetic constructs. */

  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:Id => T:Type ...</k> <tenv>... X |-> T ...</tenv>

  rule L:KLabel(T1:Type,,T2:Type) => T1 = int ~> T2 = int  ~> int
    when L ==KLabel '_+_ orBool L ==KLabel '_-_ orBool
       L ==KLabel '_*_ orBool L ==KLabel '_/_ orBool L ==KLabel '_%_
  rule - T:Type => (T = int) ~> int
  rule L:KLabel(T1:Type,,T2:Type) => T1 = int ~> T2 = int  ~> bool
    when L ==KLabel '_<_ orBool L ==KLabel '_<=_ orBool L ==KLabel '_>_ orBool
       L ==KLabel '_>=_ orBool L ==KLabel '_==_ orBool L ==KLabel '_!=_
  rule L:KLabel(T1:Type,,T2:Type) => T1 = bool ~> T2 = bool ~> bool
    when L ==KLabel '_and_ orBool L ==KLabel '_or_

  rule not T:Type => (T = bool) ~> bool
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1

/*@ \subsection{Lambda}
We add a fresh type variable for the lambda-bound variable, then we
type the lambda-body, and then we construct the corresponding function
type.  At the same time, we recover the type environment. */

  rule <k> lambda X:Id . E:Exp => freshVar(N) -> E ~> tenv(TEnv) ...</k>
          <tenv> TEnv:Map => TEnv[freshVar(N)/X] </tenv>
          <nextVar> N:Int => N +Int 1 </nextVar>

// usual environment recovery
  syntax K ::= "tenv" "(" Map ")"
  rule <k> T:Type ~> (tenv(TEnv:Map) => .) ...</k> <tenv>  _ => TEnv </tenv>
    [structural]

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

  rule <k> T1:Type T2:Type => (T1 = (T2 -> freshVar(N))) ~> freshVar(N) ...</k>
       <nextVar> N:Int => N +Int 1 </nextVar>

/*@ \subsection{Mu}
We add a fresh type variable for the mu-bound variable and then we
enforce the my-body and the result type to be both equal to the type
of the mu-bound variable. */

  rule <k> mu X:Id . E:Exp => (freshVar(N) = E) ~> freshVar(N) ~> tenv(TEnv) ...</k>
          <tenv> TEnv:Map => TEnv[freshVar(N) / X] </tenv>
          <nextVar> N:Int => N:Int +Int 1 </nextVar>

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
requiring the mgu contains only a substitutio; then we apply the
resulting most-general unifier to the let-bound type; then we bind the
let variable to the type schema obtained by parametrizing the solved
let-bound type with all its context-free type variables, that is, by
all those type variables which do not appear in types bound to other
program variables in the type environment.  The type schema construct,
as well as the \texttt{ftv} (free type variables), difference and map
application operations, are defined in the imported \texttt{TYPES}
module. */

  rule <k> let X:Id = T:Type in E:Exp => E ~> tenv(TEnv) ...</k>
       <mgu> subst(Theta:List{K}) </mgu>
       <tenv> TEnv:Map
        => TEnv[((forall diff(ftv(applySubst(subst(Theta), T),.Types),ftv(applySubst(subst(Theta), types(TEnv)))))
                 applySubst(subst(Theta), T)) / X]
       </tenv>

  rule <k> X => T[freshVars(N, |Tvs|) / Tvs]* ...</k>
       <tenv>... X:Id |-> (forall Tvs:Types) T:Type ...</tenv>
       <nextVar> N:Int => N +Int | Tvs | </nextVar>

/*@ \subsection{Final type}
When there is only one type left in the computation cell and all the
type constraints are solved, we apply the resulting mgu to that type
and that is the final result of the typing procedure. */

  rule <T>... <k> T:Type </k> <mgu> subst(Theta:List{K}) </mgu> ...</T> => <resultType> applySubst(subst(Theta), T) </resultType>

/*@ Type constraints are used to update the mgu as soon as they
are matched on the top of the computation. */

  syntax K ::= Exp "=" Exp  [strict]
  rule <k> T:Type = T':Type => . ...</k>
       <mgu> subst(Theta:List{K}) => updateMgu(subst(Theta), T, T') </mgu>

endmodule
