K Manual
========

**Under Construction**

This document contains documentation that has been written up to some extent
but still needs to be ultimately included in the K manual which has not been
written yet. New features of K that affect the surface language should be added
to this document.

Syntax Declaration
------------------

### Named Non-Terminals

We have added a syntax to Productions which allows non-terminals to be given a
name in productions. This significantly improves the ability to document K, by
providing a way to explicitly explain what a field in a production corresponds
to instead of having to infer it from a comment or from the rule body.

The syntax is:

```
name: Sort
```

This syntax can be used anywhere in a K definition that expects a non-terminal.

### `klabel(_)` and `symbol` attributes

By default K generates for each syntax definition a long and obfuscated klabel
string, which serves as internal identifier and also is used in kast format of
that syntax. If we need to reference a certain syntax production externally, we
have to manually define the klabels.

For example:

```
syntax Foo ::= #Foo( Int, Int ) [klabel(#Foo), symbol]
```

Now a kast term for `Foo` will look like `#Foo(1,  1)`.
Without `symbol`, the klabel defined for this syntax will still be a long
obfuscated string. `[symbol]` also ensures that this attribute is unique to
the definition. Uniqueness is not enforced by default for backwards
compatibility. In some circumstances in Java and Ocaml backend we need multiple
syntax definition with the same klabel. Otherwise it is recommended to use
`klabel` and `symbol` together. One application is loading a config through
JSON backend.

KLabels are also used when terms are logged in Java Backend, when using
logging/debugging options, or in error messages.

### Parametric productions and `bracket` attributes

Some syntax productions, like the rewrite operator, the bracket operator, and
the #if #then #else #fi operator, cannot have their precise type system
expressed using only concrete sorts.

Prior versions of K solved this issue by using the K sort in this case, but
this introduces inexactness in which poorly typed terms can be created even
without having a cast operator present in the syntax, which is a design
consideration we would prefer to avoid.

It also introduces cases where terms cannot be placed in positions where they
ought to be well sorted unless their return sort is made to be KBott, which in
turn vastly complicates the grammar and makes parsing much slower.

In order to introduce this, we provide a new syntax for parametric productions
in K. This allows you to express syntax that has a sort signature based on
parametric polymorphism. We do this by means of an optional curly-brace-
enclosed list of parameters prior to the return sort of a production.

Some examples:

```
syntax {Sort} Sort ::= "(" Sort ")" [bracket]
syntax {Sort} KItem ::= Sort
syntax {Sort} Sort ::= KBott
syntax {Sort} Sort ::= Sort "=>" Sort
syntax {Sort} Sort ::= "#if" Bool "#then" Sort "#else" Sort "#fi"
syntax {Sort1, Sort2} Sort1 ::= "#fun" "(" Sort2 "=>" Sort1 ")" "(" Sort2 ")"
```

Here we have:

1. Brackets, which can enclose any sort but should be of the same sort that was
   enclosed
2. Every sort is a KItem.
3. A KBott term can appear inside any sort
4. Rewrites, which can rewrite a value of any sort to a value of the same sort,
   or to a different sort which is allowed in that context
5. If then else, which can return any sort but which must contain that sort on
   both the true and false branches.
6. lambda applications, in which the argument and parameter must be the same
   sort, and the return value of the application must be the same sort as the
   return value of the function.

Note the last case, in which two different parameters are specified separated
by a comma. This indicates that we have multiple independent parameters which
must be the same each place they occur, but not the same as the other
parameters.

In practice, because every sort is a subsort of K, the `Sort2`
parameter in #6 above does nothing during parsing. It cannot
actually reject any parse, because it can always infer that the sort of the
argument and parameter are K, and it has no effect on the resulting sort of
the term. However, it will nevertheless affect the kore generated from the term
by introducing an additional parameter to the symbol generated for the term.

### `function` and `functional` attributes

Many times it becomes easier to write a semantics if you have "helper"
functions written which can be used in the RHS of rules. The `function`
attribute tells K that a given symbol should be simplified immediately when it
appears anywhere in the configuration. Semantically, it means that evaluation
of that symbol will result in at most one return value (that is, the symbol is
a *partial function*).

The `functional` attribute indicates to the symbolic reasoning engine that a
given symbol is a *total function*, that is it has *exactly* one return value
for every possible input.

For example, here we define the `_+Word_` total function and the `_/Word_`
partial function, which can be used to do addition/division modulo
`2 ^Int 256`. These functions can be used anywhere in the semantics where
integers should not grow larger than `2 ^Int 256`. Notice how `_/Word_` is
*not* defined when the denominator is `0`.

```k
syntax Int ::= Int "+Word" Int [function, functional]
             | Int "/Word" Int [function]

rule I1 +Word I2 => (I1 +Int I2) modInt (2 ^Int 256)
rule I1 /Word I2 => (I1 /Int I2) modInt (2 ^Int 256) requires I2 =/=Int 0
```

### `freshGenerator` attribute

In K, you can access "fresh" values in a given domain using the syntax
`!VARNAME:VarSort` (with the `!`-prefixed variable name). This is supported for
builtin sorts `Int` and `Id` already. For example, you can generate fresh
memory locations for declared identifiers as such:

```k
rule <k> new var x ; => . ... </k>
     <env> ENV => ENV [ x <- !I:Int ] </env>
     <mem> MEM => MEM [ !I <- 0     ] </mem>
```

Each time a `!`-prefixed variable is encountered, a new integer will be used,
so each variable declared with `new var _ ;` will get a unique position in the
`<mem>`.

Sometimes you want to have generation of fresh constants in a user-defined
sort. For this, K will still generate a fresh `Int`, but can use a converter
function you supply to turn it into the correct sort. For example, here we can
generate fresh `Foo`s using the `freshFoo(_)` function annotated with
`freshGenerator`.

```k
syntax Foo ::= "a" | "b" | "c" | d ( Int )

syntax Foo ::= freshFoo ( Int ) [freshGenerator, function, functional]

rule freshFoo(0) => a
rule freshFoo(1) => b
rule freshFoo(2) => c
rule freshFoo(I) => d(I) [owise]

rule <k> new var x ; => . ... </k>
     <env> ENV => ENV [ x <- !I:Int  ] </env>
     <mem> MEM => MEM [ !I <- !F:Foo ] </mem>
```

Now each newly allocated memory slot will have a fresh `Foo` placed in it.

Evaluation Strategy
-------------------

### `strict` and `seqstrict` attributes

The strictness attributes allow defining evaluation strategies without having
to explicitely make rules which implement them. This is done by injecting
*heating* and *cooling* rules for the subterms. For this to work, you need to
define what a *result* is for K, by extending the  `KResult` sort.

For example:

```k
syntax AExp ::= Int
              | AExp "+" AExp [strict]
```

This generates two heating rules (where the hole syntaxes `"[]" "+" AExp` and
`AExp "+" "[]"` is automatically added to create an evaluation context):

```k
rule <k> HOLE:AExp +  AE2:AExp => HOLE ~>  [] + AE2 ... </k> [heat]
rule <k>  AE1:AExp + HOLE:AExp => HOLE ~> AE1 +  [] ... </k> [heat]
```

And two corresponding cooling rules:

```k
rule <k> HOLE:AExp ~>  [] + AE2 => HOLE +  AE2 ... </k> [cool]
rule <k> HOLE:AExp ~> AE1 +  [] =>  AE1 + HOLE ... </k> [cool]
```

You will note that these rules can apply one after another infinitely. In
practice, the `KResult` sort is used to break this cycle by ensuring that only
terms that are not part of the `KResult` sort will be heated. The `heat` and 
`cool` attributes are used to tell the compiler that these are heating and
cooling rules and should be handled in the manner just described. Nothing stops
the user from writing such heating and cooling rules directly if they wish,
although we describe other more convenient syntax for most of the advanced
cases below.

One other thing to note is that in the above sentences, `HOLE` is just a
variable, but it has special meaning in the context of sentences with the
`heat` or `cool` attribute. In heating or cooling rules, the variable named
`HOLE` is considered to be the term being heated or cooled and the compiler
will generate `isKResult(HOLE)` and `notBool isKResult(HOLE)` side conditions
appropriately to ensure that the backend does not loop infinitely.

In order for this functionality to work, you need to define the `KResult` sort.
For instance, we tell K that a term is fully evaluated once it becomes an `Int`
here:

```k
syntax KResult ::= Int
```

Note that you can also say that a given expression is only strict only in
specific argument positions. Here we use this to define "short-circuiting"
boolean operators.

```k
syntax KResult ::= Bool

syntax BExp ::= Bool
              | BExp "||" BExp [strict(1)]
              | BExp "&&" BExp [strict(1)]

rule <k> true  || _    => true ... </k>
rule <k> false || REST => REST ... </k>

rule <k> true  && REST => REST  ... </k>
rule <k> false && _    => false ... </k>
```

If you want to force a specific evaluation order of the arguments, you can use
the variant `seqstrict` to do so. For example, this would make the boolean
operators short-circuit in their _second_ argument first:

```k
syntax KResult ::= Bool

syntax BExp ::= Bool
              | BExp "||" BExp [seqstrict(2,1)]
              | BExp "&&" BExp [seqstrict(2,1)]

rule <k> _    || true  => true ... </k>
rule <k> REST || false => REST ... </k>

rule <k> REST && true  => REST  ... </k>
rule <k> _    && false => false ... </k>
```

This will generate rules like this in the case of `_||_` (note that `BE1` will
not be heated unless `isKResult(BE2)` is true, meaning that `BE2` must be
evaluated first):

```k
rule <k>  BE1:BExp || HOLE:BExp => HOLE ~> BE1 ||  [] ... </k> [heat]
rule <k> HOLE:BExp ||  BE2:BExp => HOLE ~>  [] || BE2 ... </k> requires isKResult(BE2) [heat]

rule <k> HOLE:BExp ~>  [] || BE2 => HOLE ||  BE2 ... </k> [cool]
rule <k> HOLE:BExp ~> BE1 ||  [] =>  BE1 || HOLE ... </k> [cool]
```

### Context Declaration

Sometimes more advanced evaluation strategies are needed. By default, the
`strict` and `seqstrict` attributes are limited in that they cannot describe
the _context_ in which heating or cooling should occur. When this type of
control over the evaluation strategy is required, `context` sentences can be
used to simplify the process of declaring heating and cooling when it would be
unnecessarily verbose to write heating and cooling rules directly.

For example, if the user wants to heat a term if it exists under a `foo`
constructor if the term to be heated is of sort `bar`, one might write the
following context:

```k
context foo(HOLE:Bar)
```

Once again, note that `HOLE` is just a variable, but one that has special
meaning to the compiler indicating the position in the context that should
be heated or cooled.

This will automatically generate the following sentences:

```k
rule <k> foo(HOLE:Bar) => HOLE ~> foo([]) ... </k> [heat]
rule <k> HOLE:Bar ~> foo([]) => foo(HOLE) ... </k> [cool]
```

The user may also write the K cell explicitly in the context declaration
if they want to match on another cell as well, for example:

```k
context <k> foo(HOLE:Bar) ... </kl> <state> .Map </state>
```

This context will now only heat or cool if the `state` cell is empty.

### Side conditions in context declarations

The user is allowed to write a side condition in a context declaration, like
so:

```k
context foo(HOLE:Bar) requires baz(HOLE)
```

This side condition will be appended verbatim to the heating rule that is
generated, however, it will not affect the cooling rule that is generated:

```k
rule <k> foo(HOLE:Bar) => HOLE ~> foo([]) ... </k> requirese baz(HOLE) [heat]
rule <k> HOLE:Bar ~> foo([]) => foo(HOLE) ... </k> [cool]
```

### Rewrites in context declarations

The user can also include exactly one rewrite operation in a context
declaration if that rule rewrites the variable `HOLE` on the left hand side
to a term containing `HOLE` on the right hand side. For exampl;e:

```k
context foo(HOLE:Bar => bar(HOLE))
```

In this case, the code generated will be as follows:

```k
rule <k> foo(HOLE:Bar) => bar(HOLE) ~> foo([]) ... </k> [heat]
rule <k> bar(HOLE:Bar) ~> foo([]) => foo(HOLE) ... </k> [cool]
```

This can be useful if the user wishes to evaluate a term using a different
set of rules than normal.

### `result` attribute

Sometimes it is necessary to be able to evaluate a term to a different sort
than `KResult`. This is done by means of adding the `result` attribute to
a strict production, a context, or an explicit heating or cooling rule:

```k
syntax BExp ::= Bool
              | BExp "||" BExp [seqstrict(2,1), result(Bool)]
```

In this case, the sort check used by `seqstrict` and by the `heat` and `cool`
attributes will be `isBool` instead of `isKResult`. This particular example
does not really require use of the `result` attribute, but if the user wishes
to evaluate a term of sort KResult further, the result attribute would be
required.

### `hybrid` attribute

In certain situations, it is desirable to treat a particular production which
has the `strict` attribute as a result if the term has had its arguments fully
evaluated. This can be accomplished by means of the `hybrid` attribute:

```k
syntax KResult ::= Bool

syntax BExp ::= Bool
              | BExp "||" BExp [strict(1), hybrid]
```

This attribute is equivalent in this case to the following additional axiom
being added to the definition of `isKResult`:

```k
rule isKResult(BE1:BExp || BE2:BExp) => true requires isKResult(BE1)
```

### Context aliases

Sometimes it is necessary to define a fairly complicated evaluation strategy
for a lot of different operators. In this case, the user _could_ simply write
a number of complex `context` declarations, however, this quickly becomes
tedious. For this purpose, K has a concept called a _context alias_. A context
alias is a bit like a template for describing contexts. The template can then
be instantiated against particular productions using the `strict` and
`seqstrict` attributes.

Here is a (simplified) example taken from the K semantics of C++:

```k
context alias [c]: <k> HERE:K ... </k> <evaluate> false </evaluate>
context alias [c]: <k> HERE:K ... </k> <evaluate> true </evaluate> [result(ExecResult)]

syntax Expr ::= Expr "=" Init [strict(c; 1)]
```

This defines the evaluation strategy during the translation phase of a C++
program for the assignment operator. It is equivalent to writing the following
context declarations:

```k
context <k> HOLE:Expr = I:Init => HOLE ~> [] = I ... </k> <evaluate> false </evaluate>
context <k> HOLE:Expr = I:Init => HOLE ~> [] = I ... </k> <evaluate> true </evaluate> [result(ExecResult)]
```

What this is saying is, if the `evaluate` cell is false, evaluate the term
like normal to a `KResult`. But if the `evaluate` cell is true, instead
evaluate it to the `ExecResult` sort.

Essentially, we have given a name to this evaluation strategy in the form of
the rule label on the context alias sentences (in this case, `c`). We can
then say that we want to use this evaluation strategy to evaluate particular
arguments of particular productions by referring to it by name in a `strict`
attribute. For example, `strict(c)` will instantiate these contexts once for
each argument of the production, whereas `strict(c; 1)` will instantiate it
only for the first argument. The special variable `HERE` is used to tell the
compiler where you want to place the production that is to be heated or cooled.

A `strict` attribute with no rule label associated with it is equivalent to
a `strict` attribute given with the following context alias:

```k
context alias [default]: <k> HERE:K ... </k>
```

Configuration Declaration
-------------------------

### `exit` attribute

A single configuration cell containing an integer may have the "exit"
attribute. This integer will then be used as the return value on the console
when executing the program.

Rule Declaration
----------------

### Pattern Matching operator

Sometimes when you want to express a side condition, you want to say that a
rule matches if a particular term matches a particular pattern, or if it
instead does /not/ match a particular pattern.

The syntax in K for this is :=K and :/=K. It has similar meaning to ==K and
=/=K, except that where ==K and =/=K express equality, :=K and =/=K express
model membership. That is to say, whether or not the rhs is a member of the set
of terms expressed by the lhs pattern. Because the lhs of these operators is a
pattern, the user can use variables in the lhs of the operator. However, due to
current limitations, these variables are *NOT* bound in the rest of the term.
The user is thus encouraged to use anonymous variables only, although this is
not required.

This is compiled by the K frontend down to an efficient pattern matching on a
fresh function symbol.

### Anonymous function applications

There are a number of cases in K where you would prefer to be able to take some
term on the RHS, bind it to a variable, and refer to it in multiple different
places in a rule.

You might also prefer to take a variable for which you know some of its
structure, and modify some of its internal structure without requiring you to
match on every single field contained inside that structure.

In order to do this, we introduce syntax to K that allows you to construct
anonymous functions in the RHS of a rule and apply them to a term.

The syntax for this is:

```
#fun(RuleBody)(Argument)
```

Note the limitations currently imposed by the implementation. These functions
are not first-order: you cannot bind them to a variable and inject them like
you can with a regular klabel for a function. You also cannot express multiple
rules or multiple parameters, or side conditions. All of these are extensions
we would like to support in the future, however.

Some examples of how you can use these lambdas are:

```
foo(K, Record) => #fun(record(... field: _ => K))(Record)
```

```
#fun(V::Val => isFoo(V) andBool isBar(V))(someFunctionReturningVal())
```

Desugared code:

```
foo(K, Record) => lambda(Record, K)
rule lambda(record(... field: _), K) => record(... Field: K)
```

```
lambda(someFunctionReturningVal())
rule lambda(V::Val) => isFoo(V) andBool isBar(V)
```

Note in the first case that we introduce implicitly a closure here. K is bound
from outside the anonymous function and gets implicitly passed as a second
argument to the anonymous function.

### Macros and Aliases

A rule can be tagged with the `macro`, `alias`, `macro-rec`, or `alias-rec`
attributes. In all cases, what this signifies is that this is a macro rule.
Macro rules are applied statically during compilation on all terms that they
match, and statically before program execution on the initial configuration.
Currently, macros are required to not have side conditions, although they can
contain sort checks.

When a rule is tagged with the `alias` attribute, it is also applied statically
in reverse prior to unparsing on the final configuration. Note that a macro can
have unbound variables in the right hand side. When such a macro exists, it
should be used only on the left hand side of rules, unless the user is
performing symbolic execution and expects to introduce symbolic terms into the
subject being rewritten.

However, when used on the left hand side of a rule, it functions similarly to a
pattern alias, and allows the user to concisely express a reusable pattern that
they wish to match on in multiple places.

For example, consider the following semantics:

```
syntax KItem ::= "foo" | "foobar"
syntax KItem ::= bar(KItem) | baz(Int, KItem)
rule foo => foobar [alias]
rule bar(I) => baz(?_, I) [macro]
rule bar(I) => I
```

This will rewrite `baz(0, foo)` to `foo`. First `baz(0, foo)` will be rewritten
statically to `baz(0, foobar)`. Then the non-`macro` rule will apply (because
the rule will have been rewritten to `rule baz(_, I) => I`). Then `foobar` will
be rewritten statically after rewriting finishes to `foo` via the reverse form
of the alias.

Note that macros do not apply recursively within their own expansion. This is
done so as to ensure that macro expansion will always terminate. If the user
genuinely desires a recursive macro, the `macro-rec` and `alias-rec` attributes
can be used to provide this behavior.

For example, consider the following semantics:

```
syntax Exp ::= "int" Exps ";" | Exp Exp | Id
syntax Exps ::= List{Exp,","}

rule int X:Id, X':Id, Xs:Exps ; => int X ; int X', Xs ; [macro]
```

This will expand `int x, y, z;` to `int x; int y, z;` because the macro does
not apply the second time after applying the substitution of the first
application. However, if the `macro` attribute were changed to the `macro-rec`
attribute, it would instead expand (as the user likely intended) to
`int x; int y; int z;`.

The `alias-rec` attribute behaves with respect to the `alias` attribute the
same way the `macro-rec` attribute behaves with respect to `macro`.

### `anywhere` rules

Some rules are not functional, but you want them to apply anywhere in the
configuration (similar to functional rules). You can use the `anywhere`
attribute on a rule to instruct the backends to make sure they apply anywhere
they match in the entire configuration.

For example, if you want to make sure that some associative operator is always
right-associated anywhere in the configuration, you can do:

```k
syntax Stmt ::= Stmt ";" Stmt

rule (S1 ; S2) ; S3 => S1 ; (S2 ; S3) [anywhere]
```

Then after every step, all occurances of `_;_` will be re-associated. Note that
this allows the symbol `_;_` to still be a constructor, even though it is
simplified similarly to a `function`.

### `smt-lemma`, `lemma`, and `trusted` attributes

These attributes guide the prover when it tries to apply rules to discharge a
proof obligation.

-   `smt-lemma` can be applied to a rule _without_ side-conditions to encode
    that rule as an equality when sending queries to Z3.
-   `lemma` distinguishes normal rules from lemma rules in the semantics, but
    has no affect.
-   `trusted` instructs the prover that it should not attempt proving a given
    proof obligation, instead trusting that it is true.

### Projection and Predicate functions

K automatically generates certain predicate and projection functions from the
syntax you declare. For example, if you write:

```
syntax Foo ::= foo(bar: Bar)
```

It will automatically generate the following K code:

```
syntax Bool ::= isFoo(K) [function]
syntax Foo ::= "{" K "}" ":>Foo" [function]
syntax Bar ::= bar(Foo) [function]

rule isFoo(F:Foo) => true
rule isFoo(_) => false [owise]

rule { F:Foo }:>Foo => F
rule bar(foo(B:Bar)) => B
```

The first two types of functions are generated automatically for every sort in
your K definition, and the third type of function is generated automatically
for each named nonterminal in your definition. Essentially, `isFoo` for some
sort `Foo` will tell you whether a particular term of sort `K` is a `Foo`,
`{F}:>Foo` will cast `F` to sort `Foo` if `F` is of sort `Foo` and will be
undefined (i.e., theoretically defined as `#False`, the bottom symbol in
matching logic) otherwise. Finally, `bar` will project out the child of a `foo`
named `bar` in its production declaration.

Note that if another term of equal or smaller sort to `Foo` exists and has a
child named `bar` of equal or smaller sort to `Bar`, this will generate an
ambiguity during parsing, so care should be taken to ensure that named
nonterminals are sufficiently unique from one another to prevent such
ambiguities. Of course, the compiler will generate a warning in this case.


Pattern Matching
----------------

### As Patterns

New syntax has been added to K for matching a pattern and binding the resulting
match in its entirety to a variable.

The syntax is:

```
Pattern #as V::Var
```

In this case, Pattern, including any variables, is matched and the resulting
variables are added to the substitution if matching succeeds. Furthermore, the
term matched by Pattern is added to the substitution as V.

This code can also be used outside of any rewrite, in which case matching
occurs as if it appeared on the left hand side, and the right hand side becomes
a variable corresponding to the alias.

It is an error to use an as pattern on the right hand side of a rule.

### Record-like KApply Patterns

We have added a syntax for matching on KApply terms which mimics the record
syntax in functional languages. This allows us to more easily express patterns
involving a KApply term in which we don't care about some or most of the
children, without introducing a dependency into the code on the number of
arguments which could be changed by a future refactoring.

The syntax is:

```
record(... field1: Pattern1, field2: Pattern2)
```

Note that this only applies to productions that are prefix productions.
A prefix production is considered by the implementation to be any production
whose production items match the following regular expression:

```
(Terminal(_)*) Terminal("(")
(NonTerminal (Terminal(",") NonTerminal)* )?
Terminal(")")
```

In other words, any sequence of terminals followed by an open parenthesis, an
optional comma separated list of non-terminals, and a close parenthesis.

If a prefix production has no named nonterminals, a `record(...)` syntax is
allowed, but in order to reference specific fields, it is necessary to give one
or more of the non-terminals in the production names.

Note: because the implementation currently creates one production per possible
set of fields to match on, and because all possible permutations of all
possible subsets of a list of n elements is a number that scales factorially
and reaches over 100 thousand productions at n=8, we currently do not allow
fields to be matched in any order like a true record, but only in the same
order as appears in the production itself.

Given that this only reduces the number of productions to the size of the power
set, this will still explode the parsing time if we create large productions of
10 or more fields that all have names. This is something that should probably
be improved, however, productions with that large of an arity are rare, and
thus it has not been viewed as a priority.

### Or Patterns

Sometimes you wish to express that a rule should match if one out of multiple
patterns should match the same subterm. We can now express this in K by means
of using the `#Or` ML connective on the left hand side of a rule.

For example:

```
rule foo #Or bar #Or baz => qux
```

Here any of foo, bar, or baz will match this rule. Note that the behavior is
ill-defined if it is not the case that all the clauses of the or have the same
bound variables.

### Matching global context in function rules

On occasion it is highly desirable to be able to look up information from the
global configuration and match against it when evaluating a function. For this
purpose, we introduce a new syntax for function rules.

This syntax allows the user to match on *function context* from within a
function rule:

```
syntax Int ::= foo(Int) [function]

rule [[ foo(0) => I ]]
     <bar> I </bar>

rule something => foo(0)
```

This is completely desugared by the K frontend and does not require any special
support in the backend. It is an error to have a rewrite inside function
context, as we do not currently support propagating such changes back into the
global configuration. It is also an error if the context is not at the top
level of a rule body.

Desugared code:

```
syntax Int ::= foo(Int, GeneratedTopCell) [function]

rule foo(0, <generatedTop>
              <bar> I </bar>
              ...
            </generatedTop> #as Configuration) => I
rule <generatedTop>
       <k> something ... </k>
       ...
     </generatedTop> #as Configuration
  => <generatedTop>
       <k> foo(0, Configuration> ... </k>
       ...
     </generatedTop>
```

### Collection patterns

It is allowed to write patterns on the left hand side of rules which refer to
complex terms of sort Map, List, and Set, despite these patterns ostensibly
breaking the rule that terms which are functions should not appear on the left
hand side of rules. Such terms are destructured into pattern matching
operations.

The following forms are allowed:

```
// 0 or more elements followed by 0 or 1 variables of sort List followed by
// 0 or more elements
ListItem(E1) ListItem(E2) L:List ListItem(E3) ListItem(E4)

// the empty list
.List

// 0 or more elements in any order plus 0 or 1 variables of sort Set
// in any order
SetItem(K1) SetItem(K2) S::Set SetItem(K3) SetItem(K4)

// the empty set
.Set

// 0 or more elements in any order plus by 0 or 1 variables of sort Map
// in any order
K1 |-> E1 K2 |-> E2 M::Map K3 |-> E3 K4 |-> E4

// the empty map
.Map
```

Here K1, K2, K3, K4 etc can be any pattern except a pattern containing both
function symbols and unbound variables. An unbound variable is a variable whose
binding cannot be determined by means of decomposing non-set-or-map patterns or
map elements whose keys contain no unbound variables.

This is determined recursively, ie, the term `K1 |-> E2 E2 |-> E3 E3 |-> E4` is
considered to contain no unbound variables.

Note that in the pattern `K1 |-> E2 K3 |-> E4 E4 |-> E5`, K1 and K3 are
unbound, but E4 is bound because it is bound by deconstructing the key E3, even
though E3 is itself unbound.

In the above examples, E1, E2, E3, and E4 can be any pattern that is normally
allowed on the lhs of a rule.

When a map or set key contains function symbols, we know that the variables in
that key are bound (because of the above restriction), so it is possible to
evaluate the function to a concrete term prior to performing the lookup.

Indeed, this is the precise semantics which occurs; the function is evaluated
and the result is looked up in the collection.

For example:

```
syntax Int ::= f(Int) [function]
rule f(I:Int) => I +Int 1
rule <k> I:Int => . ... </k> <state> ... SetItem(f(I)) ... </state>
```

This will rewrite `I` to `.` if and only if the state cell contains
`I +Int 1`.

Note that in the case of Set and Map, one guarantee is that K1, K2, K3, and K4
represent /distinct/ elements. Pattern matching fails if the correct number of
distinct elements cannot be found.

### `all-path` and `one-path` attributes to distinguish reachability claims

As the Haskell backend can handle both one-path and all-path reachability
claims, but both these are encoded as rewrite rules in K, these attributes can
be used to clarify what kind of claim a rule is.

In addition of being able to annotate a rule with one of them
(if annotating with more at the same time, only one of them would be chosen),
one can also annotate whole modules, to give a default claim type for all rules
in that module.

Additionally, the Haskell backend introduces an extra command line option
for the K frontend, `--default-claim-type`, with possible values
`all-path` and `one-path` to allow choosing a default type for all
claims.

### Set Variables

#### Motivation

Set variables were introduced as part of Matching Mu Logic, the mathematical
foundations for K. In Matching Mu Logic, terms evaluate to sets of values.
This is useful for both capturing partiality (as in `3/0`) and capturing
non-determinism (as in `3 #Or 5`). Consequently, symbol interpretation is
extended to have a collective interpretation over sets of input values.

Usually, K rules are given using regular variables, which expect that the term
they match is both defined and has a unique interpretation.

However, it is sometimes useful to have simplification rules which work over
any kind of pattern, be it undefined or non-deterministic. This behavior can be
achieved by using set variables to stand for any kind of pattern.

#### Syntax

Any variable prefixed by `@` will be considered a set variable.

#### Example

Below is a simplification rule which motivated this extension:

```
  rule #Ceil(@I1:Int /Int @I2:Int) =>
    {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)
    [anywhere]
```

This rule basically says that `@I1:Int /Int @I2:Int` is defined if `@I1` and
`@I2` are defined and `@I2` is not 0. Using sets variables here is important as
it allows the simplification rule to apply _any_ symbolic patterns, without
caring whether they are defined or not.

This allows simplifying the expression `#Ceil((A:Int /Int B:Int) / C:Int)` to:

```
{(C =/=Int 0) #Equals true} #And #Ceil(C) #And ({(B =/=Int 0) #Equals true}
#And #Ceil(B) #And #Ceil(A)`
```

See [kframework/kore#729](https://github.com/kframework/kore/issues/729) for
more details.

#### SMT Translation

K makes queries to an SMT solver (Z3) to discharge proof obligations when doing
symbolic execution. You can control how these queries are made using the
attributes `smtlib` and `smt-hook` on declared productions.

- `smt-hook(...)` allows you to specify a term in SMTLIB2 format which should
  be used to encode that production, and assumes that all symbols appearing in
  the term are already declared by the SMT solver.
- `smtlib(...)` allows you to declare a new SMT symbol to be used when that
  production is sent to Z3, and gives it _uninterpreted function_ semantics.

```k
syntax Int ::= "~Int" Int          [function, klabel(~Int_), symbol,
                                    smtlib(notInt)]
             | Int "^%Int" Int Int [function, klabel(_^%Int__), symbol,
                                    smt-hook((mod (^ #1 #2) #3))]
```

In the example above, we declare two productions `~Int_` and `_^%Int__`, and
tell the SMT solver to:

-   use uninterpreted function semantics for `~Int_` via SMTLIB2 symbol
    `notInt`, and
-   use the SMTLIB2 term `(mod (^ #1 #2) #3)` (where `#N` marks the `N`th
    production non-terminal argument positions) for `_^%Int__`, where `mod` and
    `^` already are declared by the SMT solver.

#### Caution

Set variables are currently only supported by the Haskell backend.
The use of rules with set variables should be sound for all other backends
which just execute by rewriting, however it might not be safe for backends
which want to guarantee coverage.

Debugging
---------

The LLVM Backend has support for integration with GDB. You can run the debugger
on a particular program by passing the `--debugger` flag to krun, or by
invoking the llvm backend interpreter directly. Below we provide a simple
tutorial to explain some of the basic commands supported by the LLVM backend.

### The K Definition

Here is a sample K definition we will use to demonstrate debugging
capabilities:

```
module TEST
  imports INT

  rule [test]: I:Int => I +Int 1 requires I <Int 10

  syntax Int ::= foo(Int) [function]
  rule foo(I) => 0 -Int I

endmodule
```

You should compile this definition with `--backend llvm -ccopt -g` and without
`-ccopt -O2` in order to use the debugger most effectively.

### Stepping

**Important:** When you first run `krun` with option `--debugger`, GDB will
instruct you on how to modify ~/.gdbinit to enable printing abstract syntax
of K terms in the debugger. If you do not perform this step, you can still
use all the other features, but K terms will be printed as their raw address
in memory.

You can break before every step of execution is taken by setting a breakpoint
on the `step` function:

```
(gdb) break definition.kore:step
Breakpoint 1 at 0x25e340
(gdb) run
Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("0", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb) continue
Continuing.

Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("1", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb) continue 2
Will ignore next crossing of breakpoint 1.  Continuing.

Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("3", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb)
```

### Breaking on a specific rule

You can break when a rule is applied by giving the rule a rule label. If the
module name is TEST and the rule label is test, you can break when the rule
applies by setting a breakpoint on the `TEST.test.rhs` function:

```
(gdb) break TEST.test.rhs
Breakpoint 1 at 0x25e250: file /home/dwightguth/test/./test.k, line 4.
(gdb) run
Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that the substitution associated with that rule is visible in the
description of the frame.

You can also break when a side condition is applied using the `TEST.test.sc`
function:

```
(gdb) break TEST.test.sc
Breakpoint 1 at 0x25e230: file /home/dwightguth/test/./test.k, line 4.
(gdb) run
Breakpoint 1, TEST.test.sc (VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that every variable used in the side condition can have its value
inspected when stopped at this breakpoint, but other variables are not visible.

You can also break on a rule by its location:

```
(gdb) break test.k:4
Breakpoint 1 at 0x25e230: test.k:4. (2 locations)
(gdb) run
Breakpoint 1, TEST.test.sc (VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.sc (VarI=#token("1", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that this sets a breakpoint at two locations: one on the side condition
and one on the right hand side. If the rule had no side condition, the first
would not be set. You can also view the locations of the breakpoints and
disable them individually:

```
(gdb) info breakpoint
Num     Type           Disp Enb Address            What
1       breakpoint     keep y   <MULTIPLE>
        breakpoint already hit 3 times
1.1                         y     0x000000000025e230 in TEST.test.sc at /home/dwightguth/test/./test.k:4
1.2                         y     0x000000000025e250 in TEST.test.rhs at /home/dwightguth/test/./test.k:4
(gdb) disable 1.1
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("1", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("2", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Now only the breakpoint when the rule applies is enabled.

### Breaking on a function

You can also break when a particular function in your semantics is invoked:

```
(gdb) info functions foo
All functions matching regular expression "foo":

File /home/dwightguth/test/./test.k:
struct __mpz_struct *Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int(struct __mpz_struct *);
(gdb) break Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int
Breakpoint 1 at 0x25e640: file /home/dwightguth/test/./test.k, line 6.
(gdb) run
Breakpoint 1, Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
6         syntax Int ::= foo(Int) [function]
(gdb)
```

In this case, the variables have numbers instead of names because the names of
arguments in functions in K come from rules, and we are stopped before any
specific rule has applied. For example, `_1` is the first argument to the
function.

You can also set a breakpoint in this location by setting it on the line
associated with its production:

```
(gdb) break test.k:6
Breakpoint 1 at 0x25e640: file /home/dwightguth/test/./test.k, line 6.
(gdb) run
Breakpoint 1, Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
6         syntax Int ::= foo(Int) [function]
```

These two syntaxes are equivalent; use whichever is easier for you.

You can also view the stack of function applications:

```
(gdb) bt
#0  Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
#1  0x000000000025e5f8 in apply_rule_111 (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList)) at /home/dwightguth/test/./test.k:9
#2  0x0000000000268a52 in take_steps ()
#3  0x000000000026b7b4 in main ()
(gdb)
```

Here we see that `foo` was invoked while applying the rule on line 9 of test.k,
and we also can see the substitution of that rule. If foo was evaluated while
evaluating another function, we would also be able to see the arguments of that
function as well, unless the function was tail recursive, in which case no
stack frame would exist once the tail call was performed.

Undocumented
------------

Backend features not yet given documentation:

* Parser of KORE terms and definitions
* Term representation of K terms
* Hooked sorts and symbols
* Substituting a substitution into the RHS of a rule
  * domain values
  * functions
  * variables
  * symbols
  * polymorphism
  * hooks
  * injection compaction
  * overload compaction
* Pattern Matching / Unification of subject and LHS of rule
  * domain values
  * symbols
  * side conditions
  * and/or patterns
  * list patterns
  * nonlinear variables
  * map/set patterns
    * deterministic
    * nondeterministic
  * modulo injections
  * modulo overloads
* Stepping
  * initialization
  * termination
* Print kore terms
* Equality/comparison of terms
* Owise rules
* Strategy #STUCK axiom
* User substitution
  * binders
  * kvar

To get a complete list of hooks supported by K, you can run:

```
grep -P -R "(?<=[^-])hook\([^)]*\)" k-distribution/include/builtin/ \
     --include "*.k" -ho | \
sed 's/hook(//' | sed 's/)//' | sort | uniq | grep -v org.kframework
```

All of these hooks will also eventually need documentation.
