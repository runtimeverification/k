# Partially completed documentation

This document contains documentation that has been written up to some extent
but still needs to be ultimately included in the K manual which has not been
written yet. New features of K that affect the surface language should be
added to this document.

## As Patterns

New syntax has been added to K for matching a pattern and binding the resulting match in its entirety to a variable. The syntax is:
```
Pattern #as V::Var
```

In this case, Pattern, including any variables, is matched and the resulting variables are added to the substitution if matching succeeds. Furthermore, the term matched by Pattern is added to the substitution as V. This code can also be used outside of any rewrite, in which case matching occurs as if it appeared on the left hand side, and the right hand side becomes a variable corresponding to the alias.

## Named Non-Terminals

We have added a syntax to Productions which allows non-terminals to be given a name in productions. This significantly improves the ability to document K, by providing a way to explicitly explain what a field in a production corresponds to instead of having to infer it from a comment or from the rule body. The syntax is:
```
name: Sort
```

This syntax can be used anywhere in a K definition that expects a non-terminal.

## Record-like KApply Patterns

We have added a syntax for matching on KApply terms which mimics the record syntax in functional languages. This allows us to more easily express patterns involving a KApply term in which we don't care about some or most of the children, without introducing a dependency into the code on the number and ordering of arguments which could be changed by a future refactoring. The syntax is:

```
record(... field1: Pattern1, field2: Pattern2)
```

Note that this only applies to productions that are prefix productions. A prefix production is considered by the implementation to be any production whose production items match the following regular expression:
```
(Terminal(_)*) Terminal("(") (NonTerminal (Terminal(",") NonTerminal)* )? Terminal(")")
```
In other words, any sequence of terminals followed by an open parenthesis, an optional comma separated list of non-terminals, and a close parenthesis.

If a prefix production has no named nonterminals, a `record(...)` syntax is allowed, but in order to reference specific fields, it is necessary to give one or more of the non-terminals in the production names.

Note: because the implementation currently creates one production per possible set of fields to match on, and because all possible permutations of all possible subsets of a list of n elements is a number that scales factorially and reaches over 100 thousand productions at n=8, we currently do not allow fields to be matched in any order like a true record, but only in the same order as appears in the production itself. Given that this only reduces the number of productions to the size of the power set, this will still explode the parsing time if we create large productions of 10 or more fields that all have names. This is something that should probably be improved, however, productions with that large of an arity are rare, and thus it has not been viewed as a priority.

## Anonymous function applications

There are a number of cases in K where you would prefer to be able to take some term on the RHS, bind it to a variable, and refer to it in multiple different places in a rule. You might also prefer to take a variable for which you know some of its structure, and modify some of its internal structure without requiring you to match on every single field contained inside that structure. In order to do this, we introduce syntax to K that allows you to construct anonymous functions in the RHS of a rule and apply them to a term. The syntax for this is:

```
#fun(RuleBody)(Argument)
```

Note the limitations currently imposed by the implementation. These functions are not first-order: you cannot bind them to a variable and inject them like you can with a regular klabel for a function. You also cannot express multiple rules or multiple parameters, or side conditions. All of these are extensions we would like to support in the future, however. Some examples of how you can use these lambdas are:

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

Note in the first case that we introduce implicitly a closure here. K is bound from outside the anonymous function and gets implicitly passed as a second argument to the anonymous function.

## Poly Attribute

Some syntax productions, like the rewrite operator, the bracket operator, and the #if #then #else #fi operator, cannot have their precise type system expressed using only concrete sorts. Prior versions of K solved this issue by using the K sort in this case, but this introduces inexactness in which poorly typed terms can be created even without having a cast operator present in the syntax, which is a design consideration we would prefer to avoid. It also introduces cases where terms cannot be placed in positions where they ought to be well sorted unless their return sort is made to be KBott, which in turn vastly complicates the grammar and makes parsing much slower.

In order to introduce this, we introduce a new attribute, poly, which indicates which fields of a production are polymorphic (ie, can refer to any Sort but must refer to the same sort as each other). Some examples:

```
syntax K ::= "(" K ")" [bracket, poly(0, 1)]
syntax KItem ::= KBott [poly(1)]
syntax KItem ::= KBott [poly(0)]
syntax K ::= K "=>" K [poly(0, 1, 2)]
syntax K ::= "#if" Bool "#then" K "#else" K "#fi" [poly(0, 2, 3)]
syntax K ::= "#fun" "(" K "=>" K ")" "(" K ")" [poly(0, 2; 1, 3)]
```

Here we have:

1. Brackets, which can enclose any sort but should be of the same sort that was enclosed
2. Every sort is a KItem.
3. A KBott term can appear inside any sort
4. Rewrites, which can rewrite a value of any sort to a value of the same sort, or to a different sort which is allowed in that context
5. If then else, which can return any sort but which must contain that sort on both the true and false branches.
6. lambda applications, in which the argument and parameter must be the same sort, and the return value of the application must be the same sort as the return value of the function.

Note the last case, in which two different polymorphic sorts are specified together with the semicolon operator. This indicates that we have multiple sets of indices which must be the same as each other within each set, but not between sets. In practice, because every sort is a KItem and a KItem is a K, the (1, 3) polymorphic attribute in #6 above does nothing during parsing. It cannot actually reject any parse, because it can always infer that the sort of the argument and parameter are K, and it has no effect on the resulting sort of the term. However, it will nevertheless affect the kore generated from the term by introducing an additional parameter to the symbol generated for the term.

## Exit attribute

A single configuration cell containing an integer may have the "exit" attribute. This integer will then be used as the return value on the console when executing the program.

## Pattern Matching operator

Sometimes when you want to express a side condition, you want to say that a rule matches if a particular term matches a particular pattern, or if it instead does /not/ match a particular pattern. The syntax in K for this is :=K and :/=K. It has similar meaning to ==K and =/=K, except that where ==K and =/=K express equality, :=K and =/=K express model membership. That is to say, whether or not the rhs is a member of the set of terms expressed by the lhs pattern. Because the lhs of these operators is a pattern, the user can use variables in the lhs of the operator. However, due to current limitations, these variables are *NOT* bound in the rest of the term. The user is thus encouraged to use anonymous variables only, although this is not required. This is compiled by the K frontend down to an efficient pattern matching on a fresh function symbol.

## Or Patterns

Sometimes you wish to express that a rule should match if one out of multiple patterns should match the same subterm. We can now express this in K by means of using the `#Or` ML connective on the left hand side of a rule. For example:

```
rule foo #Or bar #Or baz => qux
```

Here any of foo, bar, or baz will match this rule. Note that the behavior is ill-defined if it is not the case that all the clauses of the or have the same bound variables.

## Matching global context in function rules

On occasion it is highly desirable to be able to look up information from the global configuration and match against it when evaluating a function. For this purpose, we introduce the `withConfig` attribute on function productions. This attribute allows the user to match on *function context* from within a function rule:

```
syntax Int ::= foo(Int) [function, withConfig]

rule [[ foo(0) => I ]]
     <bar> I </bar>

rule something => foo(0)
```

This is completely desugared by the K frontend and does not require any special support in the backend. It is an error to have a rewrite inside function context, as we do not currently support propogating such changes back into the global configuration.

Desugared code:

```
syntax Int ::= foo(Int, GeneratedTopCell) [function, withConfig]

rule foo(0, <generatedTop>... <bar> I </bar> ...</generatedTop> #as Configuration) => I
rule <generatedTop>... <k> something ...</k> ...</generatedTop> #as Configuration => <generatedTop>... <k> foo(0, Configuration> ...</k> ...</generatedTop>
```

## Macros and Aliases

A rule can be tagged with the `macro` or `alias` attribute. In both cases, what this signifies is that this is a macro rule. Macro rules are applied statically during compilation on all terms that they match, and statically before program execution on the initial configuration. Currently, macros are required to not have side conditions, although they can contain sort checks. When a rule is tagged with the `alias` attribute, it is also applied statically in reverse prior to unparsing on the final configuration. Note that a macro can have unbound variables in the right hand side. When such a macro exists, it should be used only on the left hand side of rules, unless the user is performing symbolic execution and expects to introduce symbolic terms into the subject being rewritten. However, when used on the left hand side of a rule, it functions similarly to a pattern alias, and allows the user to concisely express a reusable pattern that they wish to match on in multiple places.

For example, consider the following semantics:

```
syntax KItem ::= "foo" | "foobar"
syntax KItem ::= bar(KItem) | baz(Int, KItem)
rule foo => foobar [alias]
rule bar(I) => baz(?_, I) [macro]
rule bar(I) => I
```

This will rewrite `baz(0, foo)` to `foo`. First `baz(0, foo)` will be rewritten statically to `baz(0, foobar)`. Then the non-macro rule will apply (because the rule will have been rewritten to `rule baz(_, I) => I`). Then foobar will be rewritten statically to foo via the alias.
