
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
               > left: "mu" Id "." Exp           [latex("\mu{#1}.{#2}")]
               | "lambda" Id "." Exp       [latex("\lambda{#1}.{#2}")]
               

/*@ \subsection{Desugaring macros}
We only keep the desugaring of \texttt{letrec} into a \texttt{let}.
This way, \texttt{letrec} will also be polymorphic. */

  rule (letrec F:Id X:Id = E:Exp in E':Exp)
    => (let F = mu F . (lambda X . E) in E') [macro, anywhere]

//  syntax Exps ::= List{Exp,","}
endmodule


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

  syntax Type ::= "tv" Nat             // type variables
                | Type "->" Type        // function type
  syntax Types ::= List{Type,","}

  syntax Bool ::= "basicType" "(" Type ")"
                 | "typeVar" "(" Type ")"
  rule typeVar(T) => getKLabel(T) ==KLabel 'tv_  [structural,anywhere]

  syntax TypeSchema ::= Type
                      | "(" "forall" Types ")" Type
                          [latex("(\forall{#1}){#2}")]
  syntax TypeSchemas ::= List{TypeSchema,","}

  syntax Type ::= Type "+Type" Nat [latex("{#1}+_{\it Type}{#2}")]
  rule tv(N:Nat) +Type M:Nat => tv(N +Int M)  [structural,anywhere]

// Free type variables.  These should be generic and builtin, for all binders.
  syntax Types ::= "ftv" "(" TypeSchemas ")"
  rule ftv(BT:Type) => .Types when basicType(BT) [anywhere]
  rule ftv(Tv:Type) => Tv,.Types when typeVar(Tv) [anywhere]
  rule ftv(T1:Type -> T2:Type) => union(ftv(T1),ftv(T2)) [anywhere]
  rule ftv((forall Tvs:Types) T:Type) => diff(ftv(T),Tvs) [anywhere]
  rule ftv(.TypeSchemas) => .Types [anywhere]
  rule ftv(TS1:TypeSchema,TS2:TypeSchema,TSs:TypeSchemas)
    => union(ftv(TS1),ftv(TS2,TSs)) [anywhere]

// The operations below should be generic and builtin, for all lists
  syntax Types ::= "union" "(" Types "," Types ")"
                 | "diff" "(" Types "," Types ")"
                     [latex("{#1}-_{\it Types}{#2}")]
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
  syntax Types ::= Nat "from" Type
  rule 0 from tv(_:Nat) => .Types [anywhere]
  rule N:Nat from tv(M:Nat) => tv(M),((N -Int 1) from tv(M +Int 1)) 
    when N >Int 0
    [anywhere]

// This could also be generic: subterm relation?
  syntax Bool ::= Type "inType" Type [latex("{#1}\in_{\it Type}{#2}")]
  rule Tv:Type inType BT:Type  => false when typeVar(Tv) andBool basicType(BT) [anywhere]
  rule Tv:Type inType Tv':Type => Tv ==K Tv' when typeVar(Tv) andBool typeVar(Tv') [anywhere]
  rule Tv:Type inType (T1:Type -> T2:Type) => (Tv inType T1) orBool (Tv inType T2) [anywhere]

// Type substitution: T[Ts / Tvs]* substitutes list of types Ts for
// list of type variables Tvs.  T[T' / Tv] substitutes type T' for type
// variable Tv in T.  These should also be generic and builtin.
  syntax Type  ::= Map "[" Type  "]"   
                > Type "[" Types "/" Types "]*"  
                | Type "[" Type  "/"  Type  "]"   // auxiliary
  rule T:Type[.Types / .Types]* => T [anywhere]
  rule T:Type[T1,Ts:Types / Tv,Tvs]* => T[T1 / Tv][Ts / Tvs]* [anywhere]
  rule BT:Type[T:Type / Tv:Type] => BT when basicType(BT) andBool typeVar(Tv) [anywhere]
  rule Tv':Type[T:Type / Tv:Type] => #if Tv' ==K Tv #then T #else Tv' #fi
    when typeVar(Tv') [anywhere]
  rule (T1:Type -> T2:Type)[T:Type / Tv:Type] => (T1:Type[T:Type / Tv:Type]) -> (T2:Type[T:Type / Tv:Type]) [anywhere]

// Map application.  Should be generic and builtin.
  syntax Types ::= Map "[" Types "]*"  [prec(1)]

  rule .[T:Type] => T [anywhere]
  rule (Tv:Type |-> T':Type Theta:Map)[T:Type] => Theta[T[T'/Tv]] [anywhere]

  rule Theta:Map[.Types]* => .Types [anywhere]
  rule Theta:Map[T:Type,Ts:Types]* => Theta[T],Theta[Ts]* [anywhere]

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
  syntax Type ::= "int" | "bool"        // basic types
  rule basicType(int) => true   [structural,anywhere]
  rule basicType(bool) => true  [structural,anywhere]

/*@ \subsection{Configuration}
Besides the \textsf{k} and \textsf{tenv} cells that are also present
in IMP's type checker, we now add two more top-level cells, one for
the unification procedure and one to hold the counter for fresh type
variables.  The cell \textsf{unification} holds a cell \textsf{eqns}
with equations that need to be solved, and a cell \textsf{mgu} which
holds the current most-general unifier. */

  configuration <T color="yellow" multiplicity="?">
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
				<resultType multiplicity="?"> .K </resultType>
				
  // termination rule; useful for making sure program finished.  
  // Can be removed when we have better krun tools for displaying final config
  rule <T>... <k> T:Type </k> ...</T> => <resultType> T </resultType>

/*@ \subsection{Arithmetic expressions}
Primitive values rewrite to their types.  Arithmetic constructs, which
were all declared strict, generate type constraints for the types of
their arguments and return on the computation structure their result
type.  As seen in the unification section below, type equalities
posted on the computation structure are eventually collected and
solved by the unification procedure.  To save space and time, in the
rules below we match the \K labels corresponding to some of the
arithmetic constructs. */

  rule <k> I:Int => int ...</k>
  rule <k> B:Bool => bool ...</k>
  rule <k> X:Id => T:Type ...</k> <tenv>... X |-> T ...</tenv>

  rule <k> L:KLabel(T1:Type,,T2:Type) => (T1,T2,.Types = int,int,.Types) ~> int ...</k>
    when L ==KLabel '_+_ orBool L ==KLabel '_-_ orBool
       L ==KLabel '_*_ orBool L ==KLabel '_/_ orBool L ==KLabel '_%_
  rule <k> - T:Type => (T = int) ~> int ...</k>
  rule <k> L(T1:Type,,T2:Type) => (T1,T2,.Types = int,int,.Types) ~> bool ...</k>
    when L ==KLabel '_<_ orBool L ==KLabel '_<=_ orBool L ==KLabel '_>_ orBool
       L ==KLabel '_>=_ orBool L ==KLabel '_==_ orBool L ==KLabel '_!=_
  rule <k> L(T1:Type,,T2:Type) => (T1,T2,.Types = bool,bool,.Types) ~> bool ...</k>
    when L ==KLabel '_and_ orBool L ==KLabel '_or_

  rule <k> not T:Type => (T = bool) ~> bool ...</k>
  rule <k> if T:Type then T1:Type else T2:Type => (T,T1,.Types = bool,T2,.Types) ~> T1 ...</k>

/*@ \subsection{Lambda}
We add a fresh type variable for the lambda-bound variable, then we
type the lambda-body, and then we construct the corresponding function
type.  At the same time, we recover the type environment. */

  syntax K ::= Type "->" "[]"
  rule <k> lambda X:Id . E:Exp => E ~> (Tv -> []) ~> tenv(TEnv) ...</k>
          <tenv> TEnv:Map => TEnv[Tv/X] </tenv>
          <nextType> Tv:Type => Tv +Type 1 </nextType>
  rule T:Type ~> (Tv:Type -> []) => Tv -> T [anywhere]

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

  rule <k> T1:Type T2:Type => (T1 = (T2 -> Tv)) ~> Tv ...</k>
       <nextType> Tv:Type => Tv +Type 1 </nextType>

/*@ \subsection{Mu}
We add a fresh type variable for the mu-bound variable and then we
enforce the my-body and the result type to be both equal to the type
of the mu-bound variable. */

  syntax K ::= Type "=" "[]"
  rule <k> mu X:Id . E:Exp => E ~> (Tv:Type = []) ~> Tv ~> tenv(TEnv) ...</k>
          <tenv> TEnv:Map => TEnv[Tv / X] </tenv>
          <nextType> (Tv => Tv +Type 1) </nextType>
  rule T:Type ~> (Tv:Type = []) => Tv = T [anywhere]

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

  rule <k> let X:Id = T:Type in E:Exp => E ~> tenv(TEnv) ...</k>
       <eqns> .Bag </eqns> <mgu> Theta:Map </mgu>
       <tenv> TEnv:Map
        => TEnv[((forall diff(ftv(Theta[T]),ftv(Theta[types(TEnv)]*)))
                 Theta[T]) / X]
       </tenv>

  rule <k> X => T[|Tvs| from Tv / Tvs]* ...</k>
       <tenv>... X:Id |-> (forall Tvs:Types) T:Type ...</tenv>
       <nextType> Tv:Type => Tv +Type | Tvs | </nextType>

/*@ \subsection{Final type}
When there is only one type left in the computation cell and all the
type constraints are solved, we apply the resulting mgu to that type
and that is the final result of the typing procedure.  We also remove
the unnecessary \textsf{eqns} cell, but prefer to keep the
\textsf{mgu} cell, as it may be insightful to see its contents in the
final configuration. */

// You can remove the <mgu\> cell, too, from the final configuration
  rule <k> T:Type => Theta[T] </k> (<eqns> .Bag </eqns> => .) <mgu> Theta:Map </mgu>


/*@ \section{Unification}
Unification can be defined quite elegantly in \K (and in AC rewriting,
in general): decompose and apply the equations until each of them has
the form $x = t$ where $x$ is a variable and $t$ is a term, thus
giving us the desired most general unifier; if $t$ contains $x$ in any
of the solved equations, then unification has failed.  For
optimization reasons, we prefer to separate the already calculated
most general unifier from the equations. */

  syntax K ::= Types "=" Types  [strict]

/*@ Type constraints are added to the set of equations as soon as they
are matched on the top of the computation.  Since the mgu is held
separately, we also apply it to the type equations.  This way, we are
guaranteed that the variables in the domain of the mgu will never
appear in the equations. */
  rule <k> Ts:Types = Ts':Types => . ...</k>
       (. => <eqn> Theta[Ts]* = Theta[Ts']* </eqn>)
       <mgu> Theta:Map </mgu>

//@ Cleanup, decomposition and orientation of equations.
  rule <eqn> Ts:Types = Ts:Types </eqn> => .

  rule <eqn> (T1:Type,T2:Type,Ts:Types) = (T1':Type,T2':Type,Ts':Types) </eqn>
    => <eqn> T1 = T1' </eqn> <eqn> (T2,Ts) = (T2',Ts') </eqn>

  rule <eqn> (T1:Type -> T2:Type) = (T1':Type -> T2':Type) </eqn>
    => <eqn> T1 = T1' </eqn> <eqn> T2 = T2' </eqn>

  rule <eqn> (T:Type = Tv:Type) => (Tv = T) </eqn>
    when typeVar(Tv) andBool notBool(typeVar(T))

/*@ When an equation contains a variable, it can be added as a binding
to the mgu.  While we know that the variables in the domain of the mgu
do not appear anywhere in the equations, it can be and usually is the
case that variables appearing in the equations also appear in the
codomain of the mgu.  Thus, we have to refine the mgu by applying the
new binding to all its terms.  Moreover, to maintain the equations
canonical in terms of the current mgu, we also have to refine the
remaining equations by applying the new mgu binding to them. */

  rule <eqns> Eqns:Bag <eqn> Tv:Type = T:Type </eqn> => refine(Eqns,Tv,T) </eqns>
       <mgu> Theta => Tv |-> T refine(Theta,Tv,T) </mgu>
    when notBool(Tv inType T)

  syntax Map ::= "refine" "(" Map "," Type "," Type ")"
  rule refine(.Map,_,_) => .Map [anywhere]
  rule refine(Tv':Type|->T':Type Theta:Map, Tv:Type, T:Type)
    => Tv'|->T'[T/Tv] refine(Theta,Tv,T)
    [anywhere]

  syntax Bag ::= "refine" "(" Bag "," Type "," Type ")"
  rule refine(.Bag,Tv:Type,T:Type) => .Bag [anywhere]
  rule refine(<eqn> T1:Type = T2:Type </eqn> Eqns:Bag, Tv:Type, T:Type)
    => <eqn> T1[T/Tv] = T2[T/Tv] </eqn> refine(Eqns,Tv,T)
    [anywhere]

endmodule
