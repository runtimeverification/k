------------------------------------
--- SIMPLE-UNTYPED-SYNTAX module ---
------------------------------------

module SIMPLE-UNTYPED-SYNTAX
  tags nd

/*@ \section{Syntax}
We start by defining the SIMPLE syntax.  The language constructs discussed
above have the expected syntax and evaluation strategies.  Recall that in \K
we annotate the syntax with appropriate strictness attributes, thus giving
each language construct the desired evaluation strategy. */

/*@ \subsection{Identifiers}
The special identifier for the function ``main'' belongs to all programs.
Each program may use additional identifiers, which need to be declared either
automatically (when one uses an external parser) or manually
(when one writes the program). */

  syntax Id ::= main

/*@ \subsection{Declarations}
There are two types of declarations: for variables (including arrays) and
for functions.  As our current parser is ``algebraic'', the empty list needs
to be identifiable as a constant (unlike in CFG grammars, where it can simply
be the empty string/epsilon production).  Therefore, if only using the first
syntactic production for function declarations below, one would need to
explicitly specify the empty list constant for declaring a function with zero
arguments.  To avoid having to do that, we add a separate function declaration
production with explicitly no arguments; this will be shortly desugared into
the first one. */

  syntax Decl ::= var List{Exp} ;
                | function Id ( List{Id} ) Stmt
                | function Id ( ) Stmt

/*@ \subsection{Expressions}
The expression constructs below are standard.  Increment (\texttt{++}) takes
an expression rather than a variable because it can also increment an array
element.  Arrays can be multidimensional and can hold other arrays, so their
lookup operation takes a list of expressions as argument and applies to an
expression (which can in particular be another array lookup), respectively.
The construct \texttt{sizeof} gives the size of an array in number of elements
of its first dimension.  Like for the declaration of functions above, we have
separate syntax for function calls with zero arguments.  Note that almost all
constructs are strict.  Exceptions are the increment (since its first argument
gets updated, so it cannot be evaluated), the function call with zero
arguments (because it will get desugared), and the assignment which is only
strict in its second argument (for the same reason as the increment). */

  syntax Exp ::= Int | Bool | Id
               | ++ Exp            [prec 0]
               | Exp + Exp         [strict prec 33 gather(E e)]
               | Exp - Exp         [strict prec 33 gather(E e)]
               | Exp * Exp         [strict prec 31 gather(E e)]
               | Exp / Exp         [strict prec 31 gather(E e) nd]
               | Exp % Exp         [strict prec 31 gather(E e)]
               | - Exp             [strict]
               | Exp < Exp         [strict prec 37]
               | Exp <= Exp        [strict prec 37]
               | Exp > Exp         [strict prec 37]
               | Exp >= Exp        [strict prec 37]
               | Exp == Exp        [strict prec 37]
               | Exp != Exp        [strict prec 37]
               | Exp and Exp       [strict prec 55 gather(E e)]
               | Exp or Exp        [strict prec 59 gather(E e)]
               | not Exp           [strict prec 53]
               | Exp [ List{Exp} ] [strict prec 1]
               | sizeOf ( Exp )    [strict]
               | Exp ( )
               | Exp ( List{Exp} ) [strict prec 2]
               | read ( )
               | Exp = Exp         [strict(2) prec 40  gather (e E)]

/*@ \subsection{Statements}
Most of the statement constructs are standard for imperative languages.
We also syntactically distinguish between empty and non-empty blocks.
Variables can be declared anywhere inside a block, their scope ending
with the block.  Expressions are allowed to be used for their side-effects
only (followed by a semicolon ``\texttt{;}'').  Functions are allowed to
abruptly return.  The exceptions are parametric, i.e., one can throw a value
which is bound to the variable declared by \texttt{catch}.  Threads can be
dynamically created and terminated, and can synchronize with \texttt{acquire},
\texttt{release} and \texttt{rendezvous}.  Note that the strictness attributes
obey the intended evaluation strategy of the various constructs.  In
particular, the if-then-else construct is strict only in its first argument
(the if-then construct will be desugared into if-then-else), while the loops
constructs are not strict in any arguments. */

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


/*@ \subsection{Lists}
Currently we have to explicitly declare the syntactic lists in this
implementation of \K (they will be eventually builtin).
Note that they are associative, strict and hybrid, which means that once they
reach the top of the computation each of their elements is evaluated to a
result and the obtained list of results is automatically considered to be a
result.  We prefer to tag their units with the corresponding sort to avoid
confusion.  */

--- List{Id}; the hybrid attribute says that a list of results becomes a result
  syntax List{Id} ::= Id
                    | .List{Id} [latex "\dotCt{List\{Id\}}"]
                    | List{Id} , List{Id}
                                    [strict hybrid assoc id: .List{Id} prec 70]

--- List{Exp}
  syntax List{Exp} ::= Exp
                     | List{Id}
                     | List{Exp} , List{Exp} [ditto]

/*@ When a syntactic category extends another syntactic category,
like our \textit{Exp} which extends \textit{Id}, it is {\em strongly}
recommended that the corresponding lists over the former also extend the
corresponding lists over the latter; e.g., \textit{List\{Exp\}} above
extends \textit{List\{Id\}}.  ``Forgetting'' to add such productions
is one of the most common mistakes users of \K make when using syntactic
lists, which is one of the reasons for which we intend to automate this
process and provide builtin lists over any syntactic category in a future
version of this tool.  Until then, please pay attention to this important
syntactic detail. */

/*@ The SIMPLE syntax is complete.  Now it is a good moment to test it by
parsing dozens of SIMPLE programs.  Check the README file under k-framework
for instructions on how to do it. */
end module


module SIMPLE-UNTYPED-DESUGARED-SYNTAX
  imports SIMPLE-UNTYPED-SYNTAX 
/*@ \section{Desugared Syntax}
This module desugars some of SIMPLE's language constructs into core ones.
We only want to give semantics to core constructs, so we get rid of the
derived ones before we start the semantics.  All desugaring macros below are
straightforward.  For the semantics, we can therefore assume that all
functions take a list of arguments, that each conditional has both branches,
that there are only \texttt{while} loops, and that each variable is
declared alone and is initialized. */

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:Id = E1:Exp to E2:Exp do S)
      = {var X; X=E1; while X <= E2 do {S X=X+1;}}
  macro function F:Id() S = function F(.List{Id}) S
  macro E() = E(.List{Id})
  macro var E,E':Exp,El:List{Exp}; = var E; var E',El;
  macro var X = E; = var X; X = E;
end module
