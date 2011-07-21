
in /modules/k-visitor
in /modules/substitution

kmod SIMPLY-SUBTYPED-SYNTAX is including #ID + #INT + K
  /*@ \section*{Syntax}
  This module defines the syntax for this calculus.
  */

  // BUG: Renaming Field to FieldId or FieldName causes compilation to crash.
  sort Field

  syntax FieldType ::= Field : Type
  syntax FieldExp  ::= Field = Exp       [strict(2)]

  syntax List{Field} ::= FieldType   // BUG: See issue 189.
                       | FieldExp
                       | List{Field} , List{Field} [strict hybrid assoc prec 70]

  syntax Record ::= { List{Field} }      [strict hybrid]

  syntax BasicType ::= bool | int

  syntax Type ::= BasicType
                | Type -> Type           [prec 9 gather(e E) latex "{#1}\rightarrow{#2}"]
                | FieldType
                | Record

  syntax Exp ::= Id
               | Int
               | Bool
               | Exp Exp                 [strict prec 10 gather(E e)]
               | lambda Id : Type . Exp  [latex "\lambda{#1}\mathbin{:}{#2}\mathbin{.}{#3}"]
               | Exp . Field             [strict(1) prec 9]
               | Record

endkm

kmod SIMPLY-SUBTYPED-SEMANTICS is including SIMPLY-SUBTYPED-SYNTAX + K + SUBSTITUTION
  /*@ \section*{Static semantics}
  This module defines the static semantics for this calculus. The executable
  definition that follows essentially gives us a subtype polymorphic type checker
  for lambda calculus extended with records. 
  */

  /*@ \subsection*{Computation}
  In the static semantics, expressions represent computations and types represent
  final values, so we subsort \emph{Exp} to $\K$ and \emph{Type} to $\KResult$.
  */
  syntax K ::= Exp | List{Field}
  syntax KResult ::= Type

  /*@ \subsection*{Configuration}
  The configuration for the static semantics of this calculus consists of the
  \K cell and a cell for the typing environment.
  */
  configuration
    <T color="yellow">
      <k color="green"> .K </k>
      <tyenv color="blue"> .Map </tyenv>
    </T>

  kvar B : Bool
  kvar I : Int
  kvar X : Id
  kvar E : Exp
  kvar T T' T1 T1' T2 T2' S S' : Type
  kvar Env : Map
  kvar Fid Fid' : Field
  kvar Fs Fs' : List{Field}

  /*@ \subsection*{Basic types}
  */
  rule B => bool
  rule I => int

  /*@ \subsection*{Variable lookup}
  This rule replaces a program variable with its type in the typing
  environment.
  */
  rule <k> X => T <_/k>
       <tyenv_> X |-> T <_/tyenv>

  /*@ \subsection*{Lambda abstractions}
  */
  syntax K ::= tofunction ( Type , Map )

  rule <k> lambda X : S . E => E ~> tofunction(S, Env) <_/k>
       <tyenv> Env => Env[S / X] </tyenv>

  rule <k> T ~> tofunction(S, Env) => S -> T <_/k>
       <tyenv> _ => Env </tyenv>
  

  syntax Exp ::= Type

  /*@ \subsection*{Function application}
  */
  rule <k> (S -> T) S' => T <_/k> if S' <: S

  /*@ \subsection*{Records}
  */
  rule (Fid = T) => (Fid : T)

  /*@ \subsection*{Field access}
  */
  rule <k> { Fid : T, Fs }.Fid => T <_/k>

  /*@ \subsection*{Subtype Relation}
  */
  syntax Bool ::= Type <: Type   [latex "{#1}\mathrel{<:}{#2}"]

  /*@ Reflexivity
  */
  macro T <: T = true

  /*@ Function types
  The argument type is contravariant whereas the return type is covariant.
  */
  macro (T1 -> T1') <: (T2 -> T2') = (T2 <: T1) andBool (T1' <: T2')

  /*@ Record types
  */
  macro { Fs } <: { Fid : T } = typeof Fs Fid <: T
  macro { Fs } <: { Fid : T, Fs' } = typeof Fs Fid <: T andBool { Fs } <: { Fs' }

  /*@ Lookup a field's type. For some reason, commutative matching isn't
  working so we need to define this lookup explicitly.
  */
  syntax Type ::= typeof List{Field} Field

  macro typeof (Fid : T) Fid = T
  macro typeof (Fid : T, Fs) Fid = T
  // TODO: Conditional macros would be nice--otherwise have to use structural rules.
  rule typeof (Fid' : T, Fs) Fid => typeof Fs Fid if Fid =/=Bool Fid' [structural]

endkm

kmod SIMPLY-SUBTYPED-PROGRAMS is including SIMPLY-SUBTYPED-SEMANTICS
  /*@ \section*{Programs}
  This module defines a few programs for testing the definition.
  */

  syntax Exp ::= pgm001 | pgm002 | pgm003 | pgm004 | pgm005 | pgm006
               | pgm007 | pgm008 | pgm009 | pgm010 | pgm011 | pgm012
               | pgm013 | pgm014 | pgm015 | pgm016 | pgm017 | pgm018
               | pgm019 | pgm020 | pgm021 | pgm022 | pgm023 | pgm024

  syntax Field ::= age | height | random | foo | bar

  syntax Id ::= x | y

  /*@ All of the following programs should type check.
  */
  macro pgm001 = lambda x : int . x
  macro pgm002 = lambda x : int . ((lambda y : int . y) x)
  macro pgm003 = { age = 22 }
  macro pgm004 = { age = 22 , height = 10 }
  macro pgm005 = pgm003.age
  macro pgm006 = (lambda x : { age : int } . x.age) { age = 22 }
  macro pgm007 = (lambda x : { age : int } . x.age) { age = 22, height = 10 }
  macro pgm008 = (lambda x : { age : int } . x.age) { height = 10, age = 22 }
  macro pgm009 = (lambda x : { age : int } . { random = false }) { height = 10, age = 22 }
  macro pgm010 = (lambda x : { age : int } . { foo = x.age, random = true }) { height = 10, age = 22 }
  macro pgm011 = (lambda x : { age : int } . { foo = x, random = true }) { height = 10, age = 22 }
  macro pgm012 = { foo = (lambda x : { bar : bool } . x.bar), random = 12 }
  macro pgm013 = pgm012.foo
  macro pgm014 = lambda x : bool . lambda y : int . x
  macro pgm015 = (lambda x : { random : bool -> int -> bool } . x) { foo = true, random = pgm014 }
  macro pgm016 = lambda x : { age : int } . { age = x.age, height = 0 }
  macro pgm017 = lambda x : { age : int, foo : int } -> { height : int } . 1
  macro pgm018 = pgm017 pgm016

  // TODO: Add test programs that should not type check.

  syntax Bool ::= test001 | test002 | test003 | test004 | test005 | test006
                | test007 | test008 | test009 | test010 | test011 | test012

  /*@ The following expressions test the subtype relation.
  */
  macro test001 = { age : int } <: { age : int }
  macro test002 = { age : int , height : int } <: { age : int }
  macro test003 = { height : int , age : int } <: { age : int }
  macro test004 = { age : int } ==Bool { age : int }
  macro test005 = { height : int , age : int } ==Bool { age : int , height : int }
  macro test006 = { age : int } <: { age : int, height : int }
  macro test007 = { age : int, height : int } ==Bool { age : int, height : int }

  macro test008 = (bool -> int) <: (bool -> int)
  macro test009 = ({ age : int } -> int) <: ({ age : int, height : int } -> int)
  macro test010 = ({ age : int, foo : bool } -> int) <: ({ age : int, height : int } -> int)

  macro test011 = ({ age : int } -> { age : int, height : int }) <: ({ age : int, foo : int } -> { height : int })
  macro test012 = ({ age : int } -> { age : int, height : int }) <: ({ age : int, foo : int } -> { age : int, foo : int, height : int})

endkm

kmod SIMPLY-SUBTYPED is including SIMPLY-SUBTYPED-PROGRAMS
  /*@ \section*{Running the semantics}
  This module is the entry-point for the semantics. The macro below takes a
  program and puts it in the \K cell to execute.
  */
  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"]
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>

endkm
