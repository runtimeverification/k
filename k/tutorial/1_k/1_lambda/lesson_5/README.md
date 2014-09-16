### Adding Builtins; Side Conditions

[MOVIE [4'52"]](http://youtu.be/T1aI04q3l9U)

We have already added the builtin identifiers (sort `Id`) to LAMBDA expressions,
but those had no operations on them (note that substitution is not builtin; it
is a predefined operation, defined in K).  In this lesson we add integers and
Booleans to LAMBDA, and extend the builtin operations on them into
corresponding operations on LAMBDA expressions.  We will also learn how to add
side conditions to rules, to limit the number of instances where they can
apply.

The K tool provides several builtins, defined in the K distribution (Maude)
file k/bin/maude/lib/pl-builtins.maude, which are automatically included in all
definitions.  These can be used in the languages that we define, typically by
including them in the desired syntactic categories.  You can also define your
own builtins in case the provided ones are not suitable for your language
(e.g., the provided builtin integers and operations on them are arbitrary
precision).

For example, to add integers and Booleans as values to our LAMBDA, we have to
add the productions

    syntax Val ::= Int | Bool

`Int` and `Bool` are the nonterminals that correspond to these builtins.

To make use of these builtins, we have to add some arithmetic operation
constructs to our language.  We prefer to use the conventional infix notation
for these, and the usual precedences (i.e., multiplication and division bind
tighter than addition, which binds tighter than relational operators).
Inspired from SDF, we use `>` instead of `|` to state that all the previous
constructs bind tighter than all the subsequent ones.  See `lambda.k`.

The only thing left is to link the LAMBDA arithmetic operations to the
corresponding builtin operations, when their arguments are evaluated.
This can be easily done using trivial rewrite rules, as shown in `lambda.k`.
In general, the K tool attempts to uniformly add the corresponding builtin
name as a suffix to all the operations over builtins.  For example, the
addition over integers is an infix operation named `+Int`.

Compile the new `lambda.k` definition and evaluate some simple arithmetic
expressions.  For example, if `arithmetic.lambda` is `(1+2*3)/4 <= 1`, then

    krun arithmetic.lambda

yields, as expected,

   <k>
    true
   </k>
   <nextId>
    0
   </nextId>

Note that the parser took the desired operation precedence into account.

Let us now try to evaluate an expression which performs a wrong computation,
namely a division by zero.  Consider the expression `arithmetic-div-zero.lambda`
which is `1/(2/3)`.  Since division is strict and `2/3` evaluates to `0`, this
expression reduces to `1/0`, which further reduces to `1 /Int 0` by the rule for
division, which is now stuck (with the current Maude back-end to the K tool).

In fact, depending upon the back-end that we use to execute K definitions and
in particular to evaluate expressions over builtins, 1 /Int 0 can evaluate to
anything.  It just happens that the current Maude back-end keeps it as an
irreducible term.  Other back-ends, including future Maude back-ends, may
reduce it to an explicit error element, or issue a segmentation fault followed
by a core dump, or throw an exception, etc.

To avoid requesting the back-end to perform an illegal operation, we may use a
side condition in the rule of division, to make sure it only applies when the
denominator is non-zero.

Side conditions can only be Boolean expressions in K, which can be fully
evaluated within the underlying mathematical domains (which can be extended by
the user, as we will see in future lessons).  Side conditions cannot refer to
user-defined syntactic language constructs whose semantics is defined using K
rules, because the K rewriting machinery is not used for evaluating the side
conditions.

In other words, the K side conditions are not premises; in particular, they
cannot contain other rewrites in them (using `=>`).  This contrasts modern
rewrite engines like Maude, which allow conditional rules with rewrites in
conditions.

The rationale behind this deliberate restriction in K is twofold:
- On the one hand, general conditional rules require a complex, and thus slower
rewrite engine, which starts recursive (sometimes exhaustive) rewrite sessions
to resolve the rewrites in conditions.  In contrast, the side conditions in K
can be evaluated efficiently by back-ends, for example by evaluating builtin
expressions and/or by calling builtin functions.
- On the other hand, the semantic definitional philosophy of K is that rule
premises are unnecessary, so there is no need to provide support for them.

The above is all interesting and useful, but writing programs with just lambda
and arithmetic constructs is still a pain.  In the next two lessons we will add
let-binding and conditional constructs, which will allow us to write nicer
programs.
