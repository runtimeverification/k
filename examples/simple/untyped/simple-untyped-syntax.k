------------------------------------
--- SIMPLE-UNTYPED-SYNTAX module ---
------------------------------------

kmod SIMPLE-UNTYPED-SYNTAX is including PL-INT + PL-ID + K-LATEX

/*@ \subsection*{Identifiers}
The special identifier for the function ``main'' belongs to all programs.
Each program may use additional identifiers, which need to be declared either
automatically (when one uses an external parser) or manually (when one writes the program).
*/
  syntax Id ::= main


/*@ \subsection*{Declarations}
There are two types of declarations: for variables (including arrays) and for functions.
As syntactic sugar, functions taking zero arguments are given separate syntax, so one needs
not write the empty list constant.
*/
  syntax Decl ::= var List{Exp} ;
                | function Id ( ) Stmt
                | function Id ( List{Id} ) Stmt

/*@ \subsection*{Expressions}
The expression constructs below are standard.  Increment (\texttt{++}) takes an
expression rather than a variable because it can also increment an array element.
Arrays can be multidimensional and can hold other arrays, so their lookup operation
takes a list of expressions as argument and applies to an expression (which can
in particular be another array lookup), respectively.
The construct \texttt{sizeof} gives the size of an array in number of elements of its first dimension.
Like for the declaration of functions above, we have separate syntax for function
calls with zero arguments.
Note that almost all constructs are strict.  Exceptions are the increment (since
its first argument gets updated, so it cannot be evaluated), the function call
with zero arguments (because it will get desugared), and the assignment which
is only strict in its second argument (for the same reason as the increment).
*/
  syntax Exp ::= Int | Bool | Id
               | ++ Exp            [prec 0]
               | Exp + Exp         [strict prec 33 gather(E e)]
               | Exp - Exp         [strict prec 33 gather(E e)]
               | Exp * Exp         [strict prec 31 gather(E e)]
               | Exp / Exp         [strict prec 31 gather(E e)]
               | Exp % Exp         [strict prec 31 gather(E e)]
               | - Exp             [strict]
               | Exp < Exp         [strict prec 37]
               | Exp <= Exp        [strict prec 37]
               | Exp > Exp         [strict prec 37]
               | Exp >= Exp        [strict prec 37]
               | Exp == Exp        [strict prec 37]
               | Exp != Exp        [strict prec 37]
               | Exp and Exp       [strict prec 39 gather(E e)]
               | Exp or Exp        [strict prec 39 gather(E e)]
               | not Exp           [strict prec 38]
               | Exp [ List{Exp} ] [strict prec 1] 
               | sizeOf ( Exp )    [strict]
               | Exp ( )
               | Exp ( List{Exp} ) [strict prec 2]
               | read ( )
               | Exp = Exp         [strict(2) prec 40  gather (e E)]

/*@ \subsection*{Statements}
Most of the statement constructs are standard for imperative languages.
We also syntactically distinguish between empty and non-empty blocks.
Variables can be declared anywhere inside a block, their scope ending
with the block.
Expressions are allowed to be used for their side-effects only (followed
by a semicolon ``\texttt{;}'').
Functions are allowed to abruptly return.
The exceptions are parametric, i.e., one can throw a value which is bound
to the variable declared by \texttt{catch}.
Threads can be dynamically created and terminated, and can synchronize with
\texttt{acquire}, \texttt{release} and \texttt{rendezvous}.
Note that the strictness attributes obey the intended evaluation strategy
of the various constructs.  In particular, the if-then-else construct is
strict only in its first argument (the if-then construct will be desugared
into if-then-else), while the loops constructs are not strict in any
arguments.
*/

  syntax Stmt ::= { }
                | { Stmts }
                | Exp ;                        [strict prec 45]
                | if Exp then Stmt else Stmt   [strict(1) prec 90]
                | if Exp then Stmt             [prec 89]
                | while Exp do Stmt            [prec 90]
                | for Id = Exp to Exp do Stmt  [prec 90]
                | return Exp ;                 [strict]
                | write ( Exp ) ;              [strict]
                | try Stmt catch ( Id ) Stmt   [prec 90]
                | throw Exp ;                  [strict]
                | spawn Stmt                   [prec 90]
                | acquire Exp ;                [strict]
                | release Exp ;                [strict]
                | rendezvous Exp ;             [strict]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts                 [prec 100 gather(e E)]


-----------------------------------------------------------------------------
/*@ \subsubsection*{Lists}
Currently we have to explicitly declare the syntactic lists
(they will be eventually builtin).
Note that they are associative, strict and hybrid, which means that once they
reach the top of the computation each of their elements is evaluated to a result
and the obtained list of results is automatically considered to be a result.
We prefer to tag their units with the corresponding sort to avoid confusion.
*/
-----------------------------------------------------------------------------
--- List{Id}; the hybrid attribute says that a list of results becomes itself a result
  syntax List{Id} ::= Id
                    | .List{Id} [latex "\dotCt{List\{Id\}}"]
                    | List{Id} , List{Id} [strict hybrid assoc id: .List{Id} prec 70]

--- List{Exp}
  syntax List{Exp} ::= Exp
                     | List{Id}
                     | List{Exp} , List{Exp} [ditto]

/*@ \subsection*{Parsing programs}
The syntax of SIMPLE is now complete.  It is a good idea to test the
syntax by parsing a large variety of programs.
*/

/*@ \paragraph{Implementation-specific note:}
There are different ways to parse programs using the defined syntax.  One approach
supported in our current implementation, which we often follow, is to introduce a new
module that defines many programs as macros.  For example, in our case here, we can
introduce a module of the form\\

{\footnotesize\begin{verbatim}
kmod SIMPLE-UNTYPED-PROGRAMS is including SIMPLE-UNTYPED-SYNTAX
  syntax Id ::= f | i | t | x | y | ...
  syntax Stmts ::= pFactorial | ...

  macro pFactorial =
        var x;

        function f(y) {
          var t=1;
          for i = 1 to y do
            t = t*i;
          return t;
        }

        function main() {
          x = 5;
          write(f(f(x)));
        }

  ...
endkm\end{verbatim}}
The dots ``{\footnotesize\texttt{...}}'' above replace possibly more elements of
the same type; we only included one program in the module above, together with
all the syntactic constants it needs.  In this approach, unfortunately, the
user has to declare all these syntactic constants by hand, as above.  If one has
an external parser for the defined language, which is frequently the case when one
defines languages with more complex syntax (as the implicit parser currently
used by the \K tool is not very powerful), then one can easily modify the
external parser to generate all the necessary syntactic constants. \\
\vspace*{1ex}

As explained in the overview paper mentioned in the preamble of this
language definition, the entire language syntax is automatically included as
constructors for the builtin sort $K$ of {\em computation structures}, or simply
just {\em computations}.  Recall (see the same paper) that syntax plays no special
role in \K; that is, the application of the subsequent semantic rules takes into
account only the structure of the configuration, and not how the particular current
program or fragment of program is parsed.  That means, in particular, that the
distinction between concrete/abstract syntax and its representation as computations
of sort $K$ is irrelevant in the theory of \K.  However, it becomes quite relevant
in implementations of \K tools, because one would like to use the defined
language syntax as much as possible in the semantics, as we will do in all the
\K rules below, which means that one needs to combine a parser for the defined
language with a parser for \K in order to parse the semantic rules, which is a
highly non-trivial engineering endeavour.  In our current implementation of \K,
the internal representation of the syntactic terms follows the simple
abstract-syntax-tree (AST) syntax:
$$
K \ \ ::= \ \ \KLabel(\it List\{K\})
$$
where we use quoted identifiers with underscores for arguments and backquoted
parentheses for $\KLabel$ constants (one for each syntactic construct), e.g.,
``\texttt{'try\_catch`(\_`)\_}'', and use ``\texttt{.List\{K\}}'' and ``\texttt{,,}''
for the unit and the separator for lists of $K$ terms (to avoid conflicts with
language syntax).  For example, the internal representation of the syntactic
constant \texttt{pFactorial} above is \texttt{'pFactorial(.List\{K\})}, while
the representation of its corresponding program is

{\footnotesize\begin{verbatim}
'__('var_;('_`,_(Id x(.List{K}))),,'__('function_`(_`)_(Id f(.List{K}),
    ,'_`,_(Id y(.List{K})),,'`{_`}('__('var_;('_`,_('_=_(Id t(.List{K}),,Int 1(.List{
    K})))),,'__('for_=_to_do_(Id i(.List{K}),,Int 1(.List{K}),,Id y(.List{K}),,'_;(
    '_=_(Id t(.List{K}),,'_*_(Id t(.List{K}),,Id i(.List{K}))))),,'return_;(Id t(.List{
    K})))))),,'function_`(`)_(Id main(.List{K}),,'`{_`}('__('_;('_=_(Id x(.List{K}),,
    Int 5(.List{K}))),,'write`(_`);('_`(_`)(Id f(.List{K}),,'_`,_('_`(_`)(Id f(.List{
    K}),,'_`,_(Id x(.List{K})))))))))))
\end{verbatim}}

Our implementation allows users to use either concrete syntax (as we do) or abstract
syntax (as above) in their rules below.  We prefer the concrete syntax, but one may
need to use the abstract syntax instead when one's syntax confuses our current
(simplistic) parser.  One currently sees only abstract syntax as output
from the tool (results, or stuck computations, etc.).  Note that, in order to
enable the internal \K representation discussed above, one needs to explicitly include
the builtin module \texttt{K}.  Thus, since we did not include the module \texttt{K}
explicitly, to test the syntax one needs to either include the module \texttt{K}
as well in \texttt{SIMPLE-UNTYPED-PROGRAMS}, or better to create another module
which includes both \texttt{SIMPLE-UNTYPED-PROGRAMS} and \texttt{K}.  We prefer the
latter approach because the inclusion of module \texttt{K} automatically subsorts all
the syntactic categories to $K$, which may lead to ambiguous parsing of more complex
programs; this is, again, a limitation of our current implementation.  To check the 
internal representation of the defined programs, first compile the \K definition,
then load the generated Maude module into Maude, and then type in Maude commands
like ``\texttt{rewrite 'pFactorial(.List\{K\})}''.  */
endkm


kmod SIMPLE-UNTYPED-DESUGARED-SYNTAX is including SIMPLE-UNTYPED-SYNTAX 
/*@ This module desugars some of SIMPLE's language constructs into core ones.
We only want to give semantics to core constructs, so we get rid of the
derived ones before we start the semantics.
All desugaring macros below are straightforward.  For the semantics, we can therefore assume
that all functions take a list of arguments, that each conditional has both
branches, that there are only \texttt{while} loops, and that each variable is
declared alone and is initialized. */

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:Id = E1:Exp to E2:Exp do S) = {var X; X=E1; while X <= E2 do {S X=X+1;}}
  macro function F:Id() S = function F(.List{Id}) S
  macro E() = E(.List{Id})
  macro var E,E':Exp,El:List{Exp}; = var E; var E',El;
  macro var X; = var X=0;

/*@ \paragraph{Implementation-specific note:}
If interested in checking how these desugaring rules change the programs
already tested, then one should create a module that includes
\texttt{SIMPLE-UNTYPED-DESUGARED-SYNTAX}, \texttt{SIMPLE-UNTYPED-PROGRAMS} and
\texttt{K}, and then follow the same steps as above for checking the internal
representation of programs (without desugaring).  For example, the command
``\texttt{rewrite 'pFactorial(.List\{K\})}'' should yield the following term:\\

{\footnotesize\begin{verbatim}
'__('var_;('_`,_('_=_(Id x(.List{K}),,Int 0(.List{K})))),,'__(
    'function_`(_`)_(Id f(.List{K}),,'_`,_(Id y(.List{K})),,'`{_`}('__('var_;('_`,_(
    '_=_(Id t(.List{K}),,Int 1(.List{K})))),,'__('`{_`}('__('var_;('_`,_('_=_(Id i(
    .List{K}),,Int 0(.List{K})))),,'__('_;('_=_(Id i(.List{K}),,Int 1(.List{K}))),,
    'while_do_('_<=_(Id i(.List{K}),,Id y(.List{K})),,'`{_`}('__('_;('_=_(Id t(.List{
    K}),,'_*_(Id t(.List{K}),,Id i(.List{K})))),,'_;('_=_(Id i(.List{K}),,'_+_(Id i(
    .List{K}),,Int 1(.List{K})))))))))),,'return_;(Id t(.List{K})))))),,
    'function_`(_`)_(Id main(.List{K}),,'_`,_(.List{K}),,'`{_`}('__('_;('_=_(Id x(
    .List{K}),,Int 5(.List{K}))),,'write`(_`);('_`(_`)(Id f(.List{K}),,'_`,_('_`(_`)(Id
    f(.List{K}),,'_`,_(Id x(.List{K})))))))))))
\end{verbatim}
}
*/
endkm
