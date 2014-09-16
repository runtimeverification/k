### Selective Strictness; Anonymous Variables

[MOVIE [2'14"]](http://youtu.be/IreP6DFPWdk)

We here show how to define selective strictness of language constructs,
that is, how to state that certain language constructs are strict only
in some arguments.  We also show how to use anonymous variables.

We next define a conditional `if` construct, which takes three arguments,
evaluates only the first one, and then reduces to either the second or the
third, depending on whether the first one evaluated to true or to false.

K allows to define selective strictness using the same `strict` attribute,
but passing it a list of numbers.  The numbers correspond to the arguments
in which we want the defined construct to be strict.  In our case,

    syntax Exp ::= "if" Exp "then" Exp "else" Exp   [strict(1)]

states that the conditional construct is strict in the first argument.

We can now assume that its first argument will eventually reduce to a value, so
we only write the following two semantic rules:

    rule if true  then E else _ => E
    rule if false then _ else E => E

Thus, we assume that the first argument evaluates to either `true` or `false`.

Note the use of the anonymous variable `_`.  We use such variables purely for
structural reasons, to state that something is there but we don't care what.
An anonymous variable is therefore completely equivalent to a normal variable
which is unsorted and different from all the other variables in the rule.  If
you use `_` multiple times in a rule, they will all be considered distinct.

Compile `lambda.k` and write and execute some interesting expressions making
use of the conditional construct.  For example, the expression

    if 2<=1 then 3/0 else 10

evaluates to `10` and will never evaluate `3/0`, thus avoiding an unwanted
division-by-zero.

In the next lesson we will introduce two new language constructs, called
`let` and `letrec` and conventionally found in functional programming
languages, which will allow us to already write interesting LAMBDA programs.
