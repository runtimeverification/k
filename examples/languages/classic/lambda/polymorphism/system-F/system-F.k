in /modules/k-visitor
in /modules/substitution

kmod SYSTEM-F-SYNTAX is 
  /*@ \section*{Syntax}
  This module defines the syntax for System F.
  */

  /*@ In this implementation, we only have \texttt{int} and \texttt{bool} as
  basic types.
  */
  syntax BasicType ::= bool | int

  syntax TypeVar ::= #Id

  // TODO: the precedences and gatherings need to be adjusted to avoid excess
  // parenthesis
  syntax Type ::= BasicType
                | TypeVar
                | Type -> Type              [prec 9 gather(e E) latex "{#1}\rightarrow{#2}"]
                | forall TypeVar . Type     [latex "\mathop{\forall}{#1}\mathbin{.}{#2}"]

  sort Var

  syntax Exp ::= Var
               | Exp Exp                    [strict prec 10 gather(E e)]
               | lambda Var : Type . Exp    [latex "\lambda{#1}\mathbin{:}{#2}\mathbin{.}{#3}"]
               | lambda TypeVar . Exp       [latex "\lambda{#1}\mathbin{.}{#2}"]
               | Exp [ Type ]               [strict prec 8 latex "{#1}({#2})"] // BUG: See issue 188.
               | Type

endkm

kmod SYSTEM-F-STATIC-SEMANTICS is including SYSTEM-F-SYNTAX + K + SUBSTITUTION
  /*@ \section*{Static semantics}
  This module defines the static semantics for System F. The executable
  definition that follows essentially gives us a type checker for System F. 
  */

  /*@ \subsection*{Computation}
  In the static semantics, expressions represent computations and types
  represent final values, so we subsort \emph{Exp} to $\K$ and \emph{Type} to
  $\KResult$.
  */
  syntax K ::= Exp
  syntax KResult ::= Type
 
  /*@ \subsection*{Configuration}
  The configuration for the static semantics of System F consists of the \K
  cell and two additional cells which together form the typing environment. The
  \textsf{tyenv} cell maps program variables to types and the \textsf{tyvars}
  cell contains the set of type variables that are in scope.
  */
  configuration
    <T color="yellow">
      <k color="green"> .K </k>
      <tyenv color="blue"> .Map </tyenv>
      <tyvars color="red"> .Set </tyvars>
    </T>

  kvar X : Var
  kvar T T' T1 T2 S : Type
  kvar BT : BasicType
  kvar Tv : #Id
  kvar Tvs : Set
  kvar E E' : Exp
  kvar Env : Map

  /*@ \subsection*{Variable lookup}
  This rule replaces a program variable with its type in the typing environment
  and also checks that all the free variables in its type are in scope.
  */
  rule <k> X => T <_/k>
       <tyenv_> X |-> T <_/tyenv>
       <tyvars> Tvs </tyvars>
       if freeVars(T) -Set Tvs ==Bool .

  /*@ \subsection*{Lambda abstractions}
  */
  syntax K ::= tofunction ( Type , Map )

  rule <k> lambda X : S . E => E ~> tofunction(S, Env) <_/k>
       <tyenv> Env => Env[S / X] </tyenv>

  rule <k> T ~> tofunction(S, Env) => S -> T <_/k>
       <tyenv> _ => Env </tyenv>
  
  /*@ \subsection*{Function application}
  */
  rule <k> (S -> T) S => T <_/k>

  /*@ \subsection*{Type-level lambda abstraction}
  */
  syntax K ::= quantify TypeVar

  rule <k> lambda Tv . E => E ~> quantify(Tv) <_/k>
       <tyvars_> . => SetItem(Tv) <_/tyvars>

  rule <k> T ~> quantify(Tv) => forall Tv . T <_/k>
       <tyvars_> SetItem(Tv) => . <_/k>

  /*@ \subsection*{Type instantiation}
  */
  // TODO add free-vars condition
  rule <k> (forall Tv . T)[T'] => T[T' / Tv] <_/k>

  /*@ \subsection*{Free type variables}
  The following equations calculate the free type variables in a type.
  */
  syntax Set ::= freeVars Type
  macro freeVars(BT) = .Set
  macro freeVars(Tv) = SetItem(Tv)
  macro freeVars(T1 -> T2) = freeVars(T1) freeVars(T2)
  macro freeVars(forall Tv . T) = freeVars(T) -Set SetItem(Tv)

endkm

kmod SYSTEM-F-PROGRAMS is including SYSTEM-F-STATIC-SEMANTICS
  /*@ \section*{Programs}
  This module defines a few programs for testing the definition.
  */

  syntax #Id ::= s | t | t1 | t2 | t3
  syntax Var ::= b | f | g | i | x | y | z

  syntax Exp ::= compose | compose2 | lambdaxx | ctrue | cfalse | cnot

  syntax Exp ::= pgm001 | pgm002 | pgm003 | pgm004 | pgm005 | pgm006

  macro pgm001 = lambda x : int . x
  macro pgm002 = lambda s . lambda x : s . x
  macro pgm003 = lambda x : int . ((lambda y : int . y) x)
  macro pgm004 = lambda x : int . (lambda s . lambda y : s . y)[int] x
  macro pgm005 = lambda s . lambda x : int . (lambda y : s . y)[int] x // should fail
  macro pgm006 = lambda i : (forall s . s -> s) . lambda x : int . (i[int] x)

  //@ Function composition
  macro compose = lambda t1 . lambda t2 . lambda t3 . lambda f : t1 -> t2 . lambda g : t2 -> t3 . lambda x : t1 . (g (f x))

  //@ Function composition ``by need''
  macro compose2 = lambda t1 . lambda t2 . lambda f : t1 -> t2 . lambda t3 . lambda g : t2 -> t3 . lambda x : t1 . (g (f x))

  //@ Attempt to simulate recursion: $\lambda x . x x$
  macro lambdaxx = lambda x : (forall t . t -> t) . (x[forall t . t -> t] x)

  //@ Church booleans
  macro ctrue = lambda t . lambda x : t . lambda y : t . x
  macro cfalse = lambda t . lambda x : t . lambda y : t . y
  macro cnot = lambda b : (forall t . t -> t -> t) . lambda t . lambda x : t . lambda y : t . (b[t] y x)

endkm

kmod SYSTEM-F is including SYSTEM-F-PROGRAMS
  /*@ \section*{Running the semantics}
  This module is the entry-point for the semantics. The macro below takes a
  program and puts it in the \K cell to execute.
  */
  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"]
  macro [[KL:KLabel]] = getResult <T_> <k> KL(.List{K}) </k> <_/T>

  syntax Bag ::= getResult Bag
  syntax CellLabel ::= result
  macro getResult <T_> <k> T:Type </k> <_/T> = <result> T:Type </result>
  
endkm
