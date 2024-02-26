---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# KOOL — Typed — Static

Author: Grigore Roșu (grosu@illinois.edu)  
Organization: University of Illinois at Urbana-Champaign

Author: Traian Florin Șerbănuță (traian.serbanuta@unibuc.ro)  
Organization: University of Bucharest


## Abstract

This is the **K** static semantics of the typed KOOL language.
It extends the static semantics of typed SIMPLE with static semantics
for the object-oriented constructs.  Also, the static semantics of
some of the existing SIMPLE constructs need to change, in order to
become more generous with regards to the set of accepted programs,
mostly due to subtyping.  For example, the assignment construct
`x = e` required that both the variable `x` and the
expression `e` had the same type in SIMPLE.  In KOOL, the type
of `e` can be a subtype of the type of `x`.
Specifically, we define the following typing policy for KOOL,
everything else not mentioned below borrowing its semantics from
SIMPLE:

* Each class `C` yields a homonymous type, which can be
  explicitly used in programs to type variables and methods, possibly in
  combination with other types.

* Since now we have user-defined types, we check that each type
  used in a KOOL program is well-formed, that is, it is constructed only
  from primitive and class types corresponding to declared classes.

* Class members and their types form a **class type
  environment**.  Each class will have such a type environment.
  Each member in a class is allowed to be declared only once.  Since in
  KOOL we allow methods to be assigned to fields, we make no distinction
  between field and method members; in other words, we reject programs
  declaring both a field and a method with the same name.

* If an identifier is not found in the local type environment, it
  will be searched for in the current class type environment.  If not
  there, then it will be searched for in its superclass' type
  environment.  And so on and so forth.  If not found until the
  `Object` class is reached, a typing error is reported.

* The assignment allows variables to be assigned values of
  more concrete types.  The result type of the assignment expression
  construct will be the (more abstract) type of the assigned variable,
  and not the (more concrete) type of the expression, like in Java.

* Exceptions are changed (from SIMPLE) to allow throwing and
  catching only objects, like in Java.  Also, unlike in SIMPLE, we do
  not check whether the type of the thrown exception matches the type of
  the caught variable, because exceptions can be caught by other
  `try/catch` blocks, even by ones in other methods.  To avoid
  having to annotate each method with what exceptions it can throw, we
  prefer to not check the type safety of exceptions (although this is an
  excellent homework!).  We only check that the `try` block
  type-checks and that the `catch` block type-checks after we bind
  the caught variable to its claimed type.

* Class declarations are not allowed to have any cycles in their
  extends relation.  Such cycles would lead to non-termination of
  `new`, as it actually does in the dynamic semantics of KOOL
  where no such circularity checks are performed.

* Methods overriding other methods should be in the right subtyping
  relationship with the overridden methods: co-variant in the codomain
  and contra-variant in the domain.

```k
module KOOL-TYPED-STATIC-SYNTAX
  imports DOMAINS-SYNTAX
```

## Syntax

The syntax of statically typed KOOL is identical to that of
dynamically typed KOOL, they both taking as input the same programs.
What differs is the **K** strictness attributes.  Like in statically
typed SIMPLE, almost all language constructs are strict now, since we
want each to type its arguments almost all the time.  Like in the
other two KOOL definitions, we prefer to copy and then modify/extend
the syntax of statically typed SIMPLE.

**Note**: This paragraph is old, now we can do things better.  We keep
it here only for historical reasons, to see how much we used to suffer :)

**Annoying K-tool technical problem:**
Currently, the **K** tool treats the "non-terminal" productions (i.e.,
productions consisting of just one non-terminal), also called
"subsorting" production, differently from the other productions.
Specifically, it does not insert a node in the AST for them.  This may
look desirable at first, but it has a big problem: it does not allow
us to treat the subsort differently in different context.  For
example, since we want _`Id`_ to be both a type (a class name) and a
program variable, and since we want expressions to reduce to their
types, we are in an impossible situations in which we do not know how
to treat an identifier in the semantics: as a type, i.e., a result of
computations, or as a program variable, i.e., a non-result.  Ideally,
we would like to tag the identifiers at parse-time with their local
interpretation, but that, unfortunately, is not possible with the
current parsing capabilities of the **K** tool, because it requires to
insert additional information in the AST for the subsort productions.
This will be fixed soon.  Until then, unfortunately, we have to do the
job of the parser manually.  Instead of subsorting _`Id`_ directly
to _`Type`_, we "wrap" it first, say with a wrapper called
`class(...)`, exactly how the parser should have done.
The major drawback of this is that all the typed KOOL programs
in `kool/typed/programs` need to also be modified to always
declare class types accordingly.  The modified programs can be found
in `kool/typed/static/programs`.  So make sure you execute the
static semantics of KOOL using the modified programs.  To avoid seeing
the wrapper in the generated documentation, we associate it an
"invisibility" latex attribute below.
```k
  syntax Id ::= "Object" [token] | "Main" [token]
```

## Types

```k
  syntax Type ::= "void" | "int" | "bool" | "string"
                | Id                     [klabel("class"), symbol, avoid]  // see next
                | Type "[" "]"
                | "(" Type ")"           [bracket]
                > Types "->" Type

  syntax Types ::= List{Type,","} [overload(exps)]
```

## Declarations

```k
  syntax Param ::= Type Id
  syntax Params ::= List{Param,","}

  syntax Stmt ::= Type Exps ";" [avoid]
                | Type Id "(" Params ")" Block
                | "class" Id Block
                | "class" Id "extends" Id Block
```

## Expressions

```k
  syntax FieldReference ::= Exp "." Id          [strict(1)]
  syntax ArrayReference ::= Exp "[" Exps "]"    [strict]

  syntax Exp ::= Int | Bool | String | Id
               | "this"
               | "super"
               | "(" Exp ")"             [bracket]
               | "++" Exp
               | Exp "instanceOf" Id     [strict(1)]
               | "(" Id ")" Exp          [strict(2)]
               | "new" Id "(" Exps ")"   [strict(2)]
               > Exp "(" Exps ")"        [strict]
               | "-" Exp                 [strict]
               | "sizeOf" "(" Exp ")"    [strict]
               | "read" "(" ")"
               > left:
                 Exp "*" Exp             [strict, left]
               | Exp "/" Exp             [strict, left]
               | Exp "%" Exp             [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "!" Exp                 [strict]
               > left:
                 Exp "&&" Exp            [strict, left]
               | Exp "||" Exp            [strict, left]
               > "spawn" Block  // not strict: to check return and exceptions
               > Exp "=" Exp             [strict(2), right]

  syntax Exp ::= FieldReference | ArrayReference
  syntax priority _.__KOOL-TYPED-STATIC-SYNTAX > _[_]_KOOL-TYPED-STATIC-SYNTAX > _(_)_KOOL-TYPED-STATIC-SYNTAX

  syntax Exps ::= List{Exp,","}          [strict, overload(exps)]
```

## Statements

```k
  syntax Block ::= "{" "}"
                | "{" Stmt "}"

  syntax Stmt ::= Block
                | Exp ";"                                 [strict]
                | "if" "(" Exp ")" Block "else" Block     [avoid, strict]
                | "if" "(" Exp ")" Block                  [macro]
                | "while" "(" Exp ")" Block               [strict]
                | "for" "(" Stmt Exp ";" Exp ")" Block    [macro]
                | "return" Exp ";"                        [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"                [strict]
                | "try" Block "catch" "(" Param ")" Block [strict(1)]
                | "throw" Exp ";"                         [strict]
                | "join" Exp ";"                          [strict]
                | "acquire" Exp ";"                       [strict]
                | "release" Exp ";"                       [strict]
                | "rendezvous" Exp ";"                    [strict]

  syntax Stmt ::= Stmt Stmt                            [seqstrict, right]
```

## Desugaring macros

```k
  rule if (E) S => if (E) S else {}
  rule for(Start Cond; Step) {S:Stmt} => {Start while(Cond){S Step;}}
  rule T:Type E1:Exp, E2:Exp, Es:Exps; => T E1; T E2, Es;               [anywhere]
  rule T:Type X:Id = E; => T X; X = E;                                  [anywhere]

  rule class C:Id S => class C extends Object S

endmodule
```

## Static semantics

We first discuss the configuration, then give the static semantics
taken over unchanged from SIMPLE, then discuss the static semantics of
SIMPLE syntactic constructs that needs to change, and in the end we
discuss the static semantics and additional checks specifically
related to the KOOL proper syntax.
```k
module KOOL-TYPED-STATIC
  imports KOOL-TYPED-STATIC-SYNTAX
  imports DOMAINS
```

## Configuration

The configuration of our type system consists of a `tasks`
cell with the same meaning like in statically typed SIMPLE, of an
`out` cell streamed to the standard output that will be used to
display typing error messages, and of a cell `classes` holding
data about each class in a separate `class` cell.  The
`task` cells now have two additional optional subcells, namely
`ctenvT` and `inClass`.  The former holds a temporary
class type environment; its contents will be transferred into the
`ctenv` cell of the corresponding class as soon as all the
fields and methods in the task are processed.  In fact, there will be
three types of tasks in the subsequent semantics, each determined by
the subset of cells that it holds:

1. **Main task**, holding only a `k` cell holding the
original program as a set of classes.  The role of this task is to
process each class, generating a class task (see next) for each.

2. **Class task**, holding `k`, `ctenvT`, and
`inClass` subcells.  The role of this task type is to process
a class' contents, generating a class type environment in the
`ctenvT` cell and a method task (see next) for each method in
the class.  To avoid interference with object member lookup rules
below, it is important to add the class type environment to a class
atomically; this is the reason for which we use `ctenvT`
temporary cells within class tasks (instead of adding each member
incrementally to the class' type environment).

3. **Method task**, holding `k`, `tenv` and
`return` cells.  These tasks are similar to SIMPLE's function
tasks, so we do not discuss them here any further.

Each `class` cell hods its name (in the `className`
cell) and the name of the class it extends (in the `extends`
cell), as well as its type environment (in the `ctenv` cell)
and the set of all its superclasses (in the `extendsAll` cell).
The later is useful for example for checking whether there are cycles
in the class extends relation.
```k
  configuration <T multiplicity="?" color="yellow">
                  <tasks color="orange" multiplicity="?">
                    <task multiplicity="*" color="yellow" type="Set">
                      <k color="green"> $PGM:Stmt </k>
                      <tenv multiplicity="?" color="cyan"> .Map </tenv>
                      <ctenvT multiplicity="?" color="blue"> .Map </ctenvT>
                      <returnType multiplicity="?" color="black"> void </returnType>
                      <inClass multiplicity="?" color="Fuchsia"> .K </inClass>
                    </task>
                  </tasks>
//                  <br/>
                  <classes color="Fuchsia">
                    <classData multiplicity="*" type="Map">
                      <className color="Fuchsia"> Object </className>
                      <baseClass color="Fuchsia"> .K </baseClass>
                      <baseClasses color="Fuchsia"> .Set </baseClasses>
                      <ctenv multiplicity="?" color="blue"> .Map </ctenv>
                    </classData>
                  </classes>
                </T>
                <output color="brown" stream="stdout"> .List </output>
```

## Unchanged semantics from statically typed SIMPLE

The syntax and rules below are borrowed unchanged from statically
typed SIMPLE, so we do not discuss them much here.
```k
  syntax Exp ::= Type
  syntax Exps ::= Types
  syntax BlockOrStmtType ::= "block" | "stmt"
  syntax Type ::= BlockOrStmtType
  syntax Block ::= BlockOrStmtType
  syntax KResult ::= Type
                   | Types  // TODO: should not be needed


  context _:Type _::Exp[HOLE::Exps];

  rule T:Type E:Exp[int,Ts:Types]; => T[] E[Ts];
  rule T:Type E:Exp[.Types]; => T E;


  rule <task>... <k> _:BlockOrStmtType </k> <tenv> _ </tenv> ...</task> => .Bag


  rule _:Int => int
  rule _:Bool => bool
  rule _:String => string


  rule <k> X:Id => T ...</k> <tenv>... X |-> T ...</tenv>


  context ++(HOLE => ltype(HOLE))
  rule ++ int => int
  rule int + int => int
  rule string + string => string
  rule int - int => int
  rule int * int => int
  rule int / int => int
  rule int % int => int
  rule - int => int
  rule int < int => bool
  rule int <= int => bool
  rule int > int => bool
  rule int >= int => bool
  rule T:Type == T => bool
  rule T:Type != T => bool
  rule bool && bool => bool
  rule bool || bool => bool
  rule ! bool => bool


  rule (T[])[int, Ts:Types] => T[Ts]
  rule T:Type[.Types] => T

  rule sizeOf(_T[]) => int


  rule read() => int

  rule print(T:Type, Ts => Ts); requires T ==K int orBool T ==K string
  rule print(.Types); => stmt


  context (HOLE => ltype(HOLE)) = _


  rule <k> return; => stmt ...</k> <returnType> _ </returnType>


  rule {} => block

  rule <task> <k> {S:Stmt} => block ...</k> <tenv> Rho </tenv> R </task>
       (.Bag => <task> <k> S </k> <tenv> Rho </tenv> R </task>)

  rule _:Type; => stmt
  rule if (bool) block else block => stmt
  rule while (bool) block => stmt

  rule join int; => stmt
  rule acquire _:Type; => stmt
  rule release _:Type; => stmt
  rule rendezvous _:Type; => stmt

  syntax Stmt ::= BlockOrStmtType
  rule _:BlockOrStmtType _:BlockOrStmtType => stmt
```

## Unchanged auxiliary operations from dynamically typed SIMPLE

```k
  syntax Stmt ::= mkDecls(Params)  [function]
  rule mkDecls(T:Type X:Id, Ps:Params) => T X; mkDecls(Ps)
  rule mkDecls(.Params) => {}

  syntax LValue ::= Id
                  | FieldReference
                  | ArrayReference
  syntax Exp ::= LValue

  syntax Exp ::= ltype(Exp)
// We would like to say:
//  context ltype(HOLE:LValue)
// but we currently cannot type the HOLE
  context ltype(HOLE) requires isLValue(HOLE)

// OLD approach:
//  syntax Exp ::= ltype(Exp)  [function]
//  rule ltype(X:Id) => X
//  rule ltype(E:Exp [Es:Exps]) => E[Es]

  syntax Types ::= getTypes(Params)  [function]
  rule getTypes(T:Type _:Id) => T, .Types
  rule getTypes(T:Type _:Id, P, Ps) => T, getTypes(P,Ps)
  rule getTypes(.Params) => void, .Types
```

## Changes to the existing statically typed SIMPLE semantics

Below we give the new static semantics for language constructs that
come from SIMPLE, but whose SIMPLE static semantics was too
restrictive or too permissive and thus had to change.

## Local variable declaration

Since we can define new types in KOOL (corresponding to classes), the
variable declaration needs to now check that the claimed types exist.
The operation `checkType`, defined at the end of this module,
checks whether the argument type is correct (it actually works with
lists of types as well).
```k
  rule <k> T:Type X:Id; => checkType(T) ~> stmt ...</k>
       <tenv> Rho => Rho[X <- T] </tenv>
```

## Class member declaration

In class tasks, variable declarations mean class member declarations.
Since we reduce method declarations to variable declarations (see
below), a variable declaration in a class task can mean either a field
or a method declaration.  Unlike local variable declarations, which
can shadow previous homonymous local or member declarations, member
declarations are regarded as a set, so we disallow multiple
declarations for the same member (one could improve upon this, like in
Java, by treating members with different types or number of arguments
as different, etc., but we do not do it here).  We also issue an error
message if one attempts to redeclare the same class member.  The
framed variable declaration in the second rule below should be read
"stuck".  In fact, it is nothing but a unary operation called
`stuck`, which takes a **K**-term as argument and does nothing
with it; this `stuck` operation is displayed as a frame in this
PDF document because of its latex attribute (see the ASCII .k file,
at the end of this module).
```k
  rule <k> T:Type X:Id; => checkType(T) ~> stmt ...</k>
       <ctenvT> Rho (.Map => X |-> T) </ctenvT>
    requires notBool(X in keys(Rho))

  rule <k> T:Type X:Id; => stuck(T X;) ...</k>
       <ctenvT>... X |-> _ ...</ctenvT>
       <inClass> C:Id </inClass>
//       <br/>
       <output>... .List => ListItem("Member \"" +String Id2String(X)
                              +String "\" declared twice in class \""
                              +String Id2String(C) +String "\"!\n") </output>
```

## Method declaration

A method declaration requires two conceptual checks to be performed:
first, that the method's type is consistent with the type of the
homonymous method that it overrides, if any; and second, that its body
types correctly.  At the same time, it should also be added to the
type environment of its class.  The first conceptual task is performed
using the `checkMethod` operation defined below, and the second
by generating a corresponding method task.  To add it to the class
type environment, we take advantage of the fact that KOOL is higher
order and reduce the problem to a field declaration problem, which we
have already defined.  The role of the `ctenvT` cell in the
rule below is to structurally ensure that the method declaration takes
place in a class task (we do not want to allow methods to be declared,
for example, inside other methods).
```k
  rule <k> T:Type F:Id(Ps:Params) S
        => checkMethod(F, getTypes(Ps)->T, C')
           ~> getTypes(Ps)->T F; ...</k>
//       <br/>
       <inClass> C </inClass>
       <ctenvT> _ </ctenvT> // to ensure we are in a class pass
       <className> C </className>
       <baseClass> C' </baseClass>
//       <br/>
       (.Bag => <task>
               <k> mkDecls(Ps) S </k>
               <inClass> C </inClass>
               <tenv> .Map </tenv>
               <returnType> T </returnType>
             </task>)
```

## Assignment

A more concrete value is allowed to be assigned to a more abstract
variable.  The operation `checkSubtype` is defined at the end
of the module and it also works with pairs of lists of types.
```k
  rule T:Type = T':Type => checkSubtype(T', T) ~> T
```

## Method invocation and return

Methods can be applied on values of more concrete types than their
arguments:
```k
  rule (Ts:Types -> T:Type) (Ts':Types) => checkSubtype(Ts',Ts) ~> T
```

Similarly, we allow values of more concrete types to be returned by
methods:
```k
  rule <k> return T:Type; => checkSubtype(T,T') ~> stmt ...</k>
       <returnType> T':Type </returnType>
```

## Exceptions

Exceptions can throw and catch values of any types.  Since unlike in Java
KOOL's methods do not declare the exception types that they can throw,
we cannot test the full type safety of exceptions.  Instead, we
only check that the `try` and the `catch` statements
type correctly.
```k
  rule try block catch(T:Type X:Id) S => {T X; S}
  rule throw _T:Type ; => stmt
```

## Spawn

The spawned cell needs to also be passed the parent's class.
```k
// explain why

  rule <k> spawn S:Block => int ...</k>
       <tenv> Rho </tenv>
       <inClass> C </inClass>
       (.Bag => <task>
               <k> S </k>
               <tenv> Rho </tenv>
               <inClass> C </inClass>
             </task>)
```

## Semantics of the new KOOL constructs

## Class declaration

We process each class in the main task, adding the corresponding data
into its `class` cell and also adding a class task for it.  We
also perform some well-formedness checks on the class hierarchy.

**Initiate class processing**  
We create a class cell and a class task for each task.  Also, we start
the class task with a check that the class it extends is declared
(this delays the task until that class is processed using another
instance of this rule).
```k
// There seems to be some error with the configuration concretization,
// as the rule below does not work when rewriting . to both the task
// and the class cells; I had to include two separate . rewrites

// TODO: the following fails krun; see #2117
  rule <task> <k> class C:Id extends C':Id { S:Stmt } => stmt ...</k> </task>
       (.Bag => <classData>...
               <className> C </className>
               <baseClass> C' </baseClass>
             ...</classData>)
//       <br/>
       (.Bag => <task>
                <k> checkType(`class`(C')) ~> S </k>
                <inClass> C </inClass>
                <ctenvT> .Map </ctenvT>
             </task>)

// You may want to try the thing below, but that failed, too
/*
syntax Type ::= "stmtStop"

  rule <tasks>...
       <task> <k> class C:Id extends C':Id { S:Stmt } => stmtStop ...</k> </task>
       (.Bag => <task>
                <k> checkType(`class`(C')) ~> S </k>
                <inClass> C </inClass>
                <ctenvT> .Map </ctenvT>
             </task>)
       ...</tasks>
       <classes>...
       .Bag => <classData>...
               <className> C </className>
               <baseClass> C' </baseClass>
             ...</classData>
       ...</classes>
//       <br/>
*/
```

## Check for unique class names

```k
  rule (<T>...
          <className> C </className>
          <className> C </className>
        ...</T> => .Bag)
       <output>... .List => ListItem("Class \"" +String Id2String(C)
                                  +String "\" declared twice!\n") </output>
```
**Check for cycles in class hierarchy**  
We check for cycles in the class hierarchy by transitively closing the
class extends relation using the `extendsAll` cells, and
checking that a class will never appear in its own `extendsAll`
cell.  The first rule below initiates the transitive closure of the
superclass relation, the second transitively closes it, and the third
checks for cycles.
```k
  rule <baseClass> C </baseClass>
       <baseClasses> .Set => SetItem(C) </baseClasses>  [priority(25)]

  rule <classData>...
         <baseClasses> SetItem(C) Cs:Set (.Set => SetItem(C')) </baseClasses>
       ...</classData>
       <classData>... <className>C</className> <baseClass>C'</baseClass> ...</classData>
    requires notBool(C' in (SetItem(C) Cs))  [priority(25)]

  rule (<T>...
          <className> C </className>
          <baseClasses>... SetItem(C) ...</baseClasses>
        ...</T> => .Bag)
       <output>... .List => ListItem("Class \"" +String Id2String(C)
                                  +String "\" is in a cycle!\n") </output>
    [group(inheritance-cycle), priority(25)]
```

## New

To type `new` we only need to check that the class constructor
can be called with arguments of the given types, so we initiate a call
to the constructor method in the corresponding class.  If that
succeeds, meaning that it types to `stmt`, then we discard the
`stmt` type and produce instead the corresponding class type of
the new object.  The auxiliary `discard` operation is defined
also at the end of this module.
```k
  rule new C:Id(Ts:Types) => `class`(C) . C (Ts) ~> discard ~> `class`(C)
```

## Self reference

The typing rule for `this` is straightforward: reduce to the
current class type.
```k
  rule <k> this => `class`(C) ...</k>
       <inClass> C:Id </inClass>
```

## Super

Similarly, `super` types to the parent class type.
Note that for typing concerns, super can be considered as an object
(recall that this was not the case in the dynamic semantics).
```k
   rule <k> super => `class`(C') ...</k>
        <inClass> C:Id </inClass>
        <className> C </className>
        <baseClass> C':Id </baseClass>
```

## Object member access

There are several cases to consider here.  First, if we are in a class
task, we should lookup the member into the temporary class type
environemnt in cell `ctenvT`.  That is because we want to allow
initialized field declarations in classes, such as `int x=10;`.
This is desugared to a declaration of `x`, which is added to
`ctenvT` during the class task processing, followed by an
assignment of `x` to 10.  In order for the assignment to type
check, we need to know that `x` has been declared with type
`int`; this information can only be found in the
`ctenvT` cell.  Second, we should redirect non-local variable
lookups in method tasks to corresponding member accesses (the
local variables are handled by the rule borrowed from SIMPLE).
This is what the second rule below does.  Third, we should allow
object member accesses as lvalues, which is done by the third rule
below.  These last two rules therefore ensure that each necessary
object member access is explicitly allowed for evaluation.  Recall
from the annotated syntax module above that the member access
operation is strict in the object.  That means that the object is
expected to evaluate to a class type.  The next two rules below define
the actual member lookup operation, moving the search to the
superclass when the member is not found in the current class.  Note
that this works because we create the class type environments
atomically; thus, a class either has its complete type environment
available, in which case these rules can safely apply, or its cell
`ctenv` is not yet available, in which case these rules have to
wait.  Finally, the sixth rule below reports an error when the
`Object` class is reached.
```k
  rule <k> X:Id => T ...</k>
       <ctenvT>... X |-> T ...</ctenvT>

  rule <k> X:Id => this . X ...</k>
       <tenv> Rho </tenv>
    requires notBool(X in keys(Rho))

// OLD approach:
//  rule ltype(E:Exp . X:Id) => E . X

  rule <k> `class`(C:Id) . X:Id => T ...</k>
       <className> C </className>
       <ctenv>... X |-> T:Type ...</ctenv>

  rule <k> `class`(C1:Id => C2) . X:Id ...</k>
       <className> C1 </className>
       <baseClass> C2:Id </baseClass>
       <ctenv> Rho </ctenv>
    requires notBool(X in keys(Rho))

  rule <k> `class`(Object) . X:Id => stuck(`class`(Object) . X) ...</k>
       <inClass> C:Id </inClass>
//      <br/>
       <output>... .List => ListItem("Member \"" +String Id2String(X)
                              +String "\" not declared! (see class \""
                              +String Id2String(C) +String "\")\n") </output>
```

## Instance of and casting

As it is hard to check statically whether casting is always safe,
the programmer is simply trusted from a typing perspective.  We only
do some basic upcasting and downcasting checks, to reject casts which
will absolutely fail.  However, dynamic semantics or implementations
of the language need to insert runtime checks for downcasting to be safe.
```k
  rule `class`(_C1:Id) instanceOf _C2:Id => bool
  rule (C:Id) `class`(C) => `class`(C)
  rule <k> (C2:Id) `class`(C1:Id) => `class`(C2) ...</k>
       <className> C1 </className>
       <baseClasses>...SetItem(C2)...</baseClasses>    // upcast
  rule <k> (C2:Id) `class`(C1:Id) => `class`(C2) ...</k>
       <className> C2 </className>
       <baseClasses>...SetItem(C1)...</baseClasses>    // downcast
  rule <k> (C2) `class`(C1:Id) => stuck((C2) `class`(C1)) ...</k>
       <classData>...
         <className> C1 </className>
         <baseClasses> S1 </baseClasses>
       ...</classData>
       <classData>...
         <className> C2 </className>
         <baseClasses> S2 </baseClasses>
       ...</classData>
       <output>... .List => ListItem("Classes \"" +String Id2String(C1)
                              +String "\" and \"" +String Id2String(C2)
                              +String "\" are incompatible!\n") </output>
    requires notBool(C1 in S2) andBool notBool(C2 in S1)
```

## Cleanup tasks

Finally, we need to clean up the terminated tasks.  Each of the three
types of tasks is handled differently.  The main task is replaced by a
method task holding `new main();`, which will ensure that a
`main` class with a `main()` method actually exists
(first rule below).  A class task moves its temporary class type
environment into its class' cell, and then it dissolves itself (second
rule).  A method task simply dissolves when terminated (third rule);
the presence of the `tenv` cell in that rule ensures that that
task is a method task.
Finally, when all the tasks are cleaned up, we can also remove the
`tasks` cell, issuing a corresponding message.  Note that
checking for cycles or duplicate methods can still be performed after
the `tasks` cell has been removed.
```k
// discard main task when done, issuing a "new main();" command to
// make sure that the class main and the method main() are declared.

  rule <task> <k> stmt => new Main(.Exps); </k>
              (.Bag => <tenv> .Map </tenv>
                    <returnType> void </returnType>
                    <inClass> Main </inClass>)
       </task>

// discard class task when done, adding a ctenv in class

  rule (<task>
          <k> stmt </k>
          <ctenvT> Rho </ctenvT>
          <inClass> C:Id </inClass>
        </task> => .Bag)
        <className> C </className>
        (.Bag => <ctenv> Rho </ctenv>)

// discard method task when done

  rule <task>...
         <k> stmt </k>
         <tenv> _ </tenv>  // only to ensure that this is a method task
       ...</task> => .Bag

// cleanup tasks and output a success message when done

  rule (<T>... <tasks> .Bag </tasks> ...</T> => .Bag)
       <output>... .List => ListItem("Type checked!\n") </output>
```

## KOOL-specific auxiliary declarations and operations

## Subtype checking

The subclass relation introduces a subtyping relation.
```k
  syntax KItem ::= checkSubtype(Types,Types)

  rule checkSubtype(T:Type, T) => .K

  rule <k> checkSubtype(`class`(C:Id), `class`(C':Id)) => .K ...</k>
       <className> C </className>
       <baseClasses>... SetItem(C') ...</baseClasses>

  rule checkSubtype(Ts1->T2,Ts1'->T2')
    => checkSubtype(((T2)::Type,Ts1'),((T2')::Type,Ts1))

// note that the following rule would be wrong!
//  rule checkSubtype(T[],T'[]) => checkSubtype(T,T')

  rule checkSubtype((T:Type,Ts),(T':Type,Ts'))
    => checkSubtype(T,T') ~> checkSubtype(Ts,Ts')
    requires Ts =/=K .Types

  rule checkSubtype(.Types,.Types) => .K
  rule checkSubtype(.Types,void) => .K
```

## Checking well-formedness of types

Since now any _`Id`_ can be used as the type of a class, we need to
check that the types used in the program actually exists
```k
  syntax KItem ::= checkType(Types)

  rule checkType(T:Type,Ts:Types) => checkType(T) ~> checkType(Ts)
    requires Ts =/=K .Types
  rule checkType(.Types) => .K
  rule checkType(int) => .K
  rule checkType(bool) => .K
  rule checkType(string) => .K
  rule checkType(void) => .K
  rule <k> checkType(`class`(C:Id)) => .K ...</k> <className> C </className>
  rule checkType(`class`(Object)) => .K
  rule checkType(Ts:Types -> T:Type) => checkType(T,Ts)
  rule checkType(T:Type[]) => checkType(T)
```

## Checking correct  overiding of methods

The `checkMethod` operation below searches to see whether
the current method overrides some other method in some superclass.
If yes, then it issues an additional check that the new method's type
is more concrete than the overridden method's.  The types `T` and `T'`
below can only be function types.  See the definition of
`checkSubtype` on function types at the end of this module (it
is co-variant in the codomain and contra-variant in the domain).
```k
  syntax KItem ::= checkMethod(Id,Type,Id)

  rule <k> checkMethod(F:Id, T:Type, C:Id) => checkSubtype(T, T') ...</k>
       <className> C </className>
       <ctenv>... F |-> T':Type ...</ctenv>

  rule <k> checkMethod(F:Id, _T:Type, (C:Id => C')) ...</k>
       <className> C </className>
       <baseClass> C':Id </baseClass>
       <ctenv> Rho </ctenv>
    requires notBool(F in keys(Rho))

  rule checkMethod(_:Id,_,Object) => .K
```

## Generic operations which could be part of the **K** framework

```k
  syntax KItem ::= stuck(K)

  syntax KItem ::= "discard"
  rule _:KResult ~> discard => .K

endmodule
```
