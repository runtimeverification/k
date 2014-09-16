### Syntax Modules and Basic K Commands

[MOVIE [4'07"]](http://youtu.be/y5Tf1EZVj8E)

Here we define our first K module, which contains the initial syntax of LAMBDA,
and learn how to use the basic K commands.

I have just created an empty working folder, and opened a terminal window
(to the left) and an editor window (to the right).  We will edit our K
definition in the right window in a file called `lambda.k`, and will call
the K tool commands in the left window.

Let us start by defining a K module, containing the syntax of LAMBDA.

K modules are introduced with the keywords `module` ... `endmodule`.

The keyword `syntax` adds new productions to the syntax grammar, using a
BNF-like notation.

Terminals are enclosed in double-quotes, like strings.

You can define multiple productions for the same non-terminal in the same
syntax declaration using the `|` separator.

Productions can have attributes, which are enclosed in square brackets.

The attribute `left` tells the parser that we want the lambda application to be
left associative.  For example, `a b c d` will then parse as `(((a b) c) d)`.

The attribute `bracket` tells the parser to not generate a node for the
parenthesis production in the abstract syntax trees associated to programs.
In other words, we want to allow parentheses to be used for grouping, but we
do not want to bother to give them their obvious (ignore) semantics.

In our variant of lambda calculus defined here, identifiers and lambda
abstractions are meant to be irreducible, that is, are meant to be values.
However, so far `Val` is just another non-terminal, just like `Exp`,
without any semantic meaning.  It will get a semantic meaning later.

After we are done typing our definition in the file `lambda.k`, we can kompile
it with the command:

    kompile lambda.k

If we get no errors then a parser has been generated.  This parser will be
called from now on by default by the krun tool.  To see whether and how the
parser works, we are going to write some LAMBDA programs and store them in
files with the extension `.lambda`.

Let us create a file `identity.lambda`, which contains the identity lambda
abstraction:

    lambda x . x

Now let us call `krun` on `identity.lambda`:

    krun identity.lambda

Make sure you call the `krun` command from the folder containing your language
definition (otherwise type `krun --help` to learn how to pass a language
definition as a parameter to `krun`).  The krun command produces the output:

    <k>
      lambda x . x 
    </k>

If you see such an output it means that your program has been parsed (and then
pretty printed) correctly.  If you want to see the internal abstract syntax
tree (AST) representation of the parsed program, which we call the K AST, then
type `kast` in the command instead of `krun`:

    kast identity.lambda

You should normally never need to see this internal representation in your
K definitions, so do not get scared (yes, it is ugly for humans, but it is
very convenient for tools).

Note that `krun` placed the program in a `<k> ... </k>` cell.  In K, computations
happen only in cells.  If you do not define a configuration in your definition,
like we did here, then a configuration will be created automatically for you
which contains only one cell, the default `k` cell, which holds the program.

Next, let us create a file `free-variable-capture.lambda`, which contains an
expression which, in order to execute correctly in a substitution-based
semantics of LAMBDA, the substitution operation needs to avoid
variable-capture:

    a (((lambda x.lambda y.x) y) z)

Next, file `closed-variable-capture.lambda` shows an expression which also
requires a capture-free substitution, but this expression is closed (that is,
it has no free variables) and all its bound variables are distinct (I believe
this is the smallest such expression):

    (lambda z.(z z)) (lambda x.lambda y.(x y))

Finally, the file `omega.lambda` contains the classic omega combinator
(or closed expression), which is the smallest expression which loops forever
(not now, but after we define the semantics of LAMBDA):

    (lambda x.(x x)) (lambda x.(x x))

Feel free to define and parse several other LAMBDA programs to get a feel for
how the parser works.  Parse also some incorrect programs, to see how the
parser generates error messages.

In the next lesson we will see how to define semantic rules that iteratively
rewrite expressions over the defined syntax until they evaluate to a result.
This way, we obtain our first programming language defined using K.
