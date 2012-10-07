//
// WARNING
//
// This is a heavily commented K definition, part of the K
// tutorial.

/*!
\setlength{\parindent}{1em}
\title{IMP++}
\author{Grigore Ro\c{s}u (\texttt{grosu@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
This is the \K semantic definition of the IMP++ language.
IMP++ extends the IMP language with the features listed below.  We
strongly recommend you to first familiarize yourself with the IMP
language and its \K definition before proceeding.
\begin{description}
\item [Strings and concatenation of strings.]  Strings are useful
for the \texttt{print} statement, which is discussed below.  For
string concatenation, we use the same \texttt{+} construct that we use
for addition.
\item [Variable increment.]  We only add a pre-increment construct:
\texttt{++x} increments variable \texttt{x} and evaluates to the
incremented value.  Variable increment makes the evaluation of
expressions have side effects, and thus makes the evaluation strategies
of the various language constructs have an influence on the set
of possible program behaviors.
\item [Input and output.]  IMP++ adds a \texttt{read()} expression
construct which reads an integer number and evaluates to it, and 
a variadic (i.e., it has an arbitrary number of arguments) statement
construct \texttt{print(e1,e2,...,en)} which evaluates its arguments
and then outputs their values.  Note that the \K tool allows to
connect the input and output cells to the standard input and output
buffers, this way compiling the language definition into an
interactive interpreter.
\item [Abrupt termination.]  The \texttt{halt} statement simply halts
the program.  The \K tool shows the resulting configuration, as if the
program terminated normally.  We therefore assume that an external
observer does not care whether the program terminates normally or
abruptly, same like with \texttt{exit} statements in conventional
programming languages like C\@.
\item [Dynamic threads.] The statement \texttt{spawn s} starts a new
concurrent thread that executes statement \texttt{s}.  The newly
created thread is given at creation time the {\em environment} of its
parent, so it can access all its parent's variables.  This allows for
the parent thread and the child thread to communicate; it also allows
for races and ``unexpected'' behaviors, so be careful.
For simplicity, we here assume a sequentially consistent shared memory
model.  To experiment with other memory models, see the definition of
KERNELC\@.
\item [Blocks and local variables.]  IMP++ allows blocks enclosed by 
curly brackets.  Also, IMP's global variable declaration construct is
generalized to be used anywhere as a statement, not only at the
beginning of the program.  As expected, the scope of the declared
variables is from their declaration point till the end of the most
nested enclosing block.
\end{description} 

\section{What You Will Learn Here}

\begin{itemize}
\item How to define a less trivial language in \K, as explained above.
\item How to use the \texttt{superheat} and \texttt{supercool}
options of the \K tool \texttt{kompile} to exhaustively explore the
non-determinism due to underspecified evaluation strategies.
\item How to use the \texttt{transition} option of the \K tool to
exhaustively explore the non-determinism due to concurrency.
\item How to connect certain cells in the configuration to the
standard input and standard output, and thus turn the \texttt{krun}
tool into an interactive interpreter for the defined language.
\item How to exhaustively search for the non-deterministic behaviors
of a program using the \texttt{search} option of \texttt{krun}.
\end{itemize}
*/

module IMP-SYNTAX
/*@ \section{Syntax}
IMP++ adds several syntactic constructs to IMP\@.  Also, since the
variable declaration construct is generalized to be used anywhere a
statement can be used, not only at the beginning of the program, we
need to remove the previous global variable declaration of IMP and
instead add a variable declaration statement construct

We do not re-discuss the constructs which are taken over from IMP\@;
go the last lesson of Tutorial 2 if you are interested in those.
For execution purposes, we tag the addition and division operations
with the \texttt{addition} and \texttt{division} tags.
These attributes have no theoretical significance, in that they
does not affect the semantics of the language in any way.  They only have
practical relevance, specific to our implementation of the \K tool.
Specifically, we can tell the \K tool (using its \texttt{superheat} and
\texttt{supercool} options) that we want to exhaustively explore
all the non-deterministic behaviors (due to strictness) of these
language constructs.  For performance reasons, by default the \K tool
chooses an arbitrary but fixed order to evaluate the arguments of the strict
language constructs, thus possibly losing behaviors due to missed
interleavings.  This aspect was irrelevant in IMP, because its expressions
had no side effects, but it becomes relevant in IMP++\@. 

The syntax of the IMP++ constructs is self-explanatory.
Note that \texttt{print} is variadic, taking a list of expressions as
argument.  It is also strict, which means that the entire list of
expressions, that is, each expression in the list, will be evaluated.
Note also that we have a special \texttt{\{\}} construct for empty
blocks, in addition to a general \texttt{\{$\it Stmt$\}} block
construct.  To have only one block construct, we would need to define
semicolon-separated lists of statements with a construct of the form
``${\it Stmts} ::= {\it List}\{{\it Stmt},{\it ";"}\}$'',
and then define the syntax of blocks as \texttt{\{$\it Stmts$\}}.
However, several other changes would be needed in order to do that, so
we prefer to keep two different syntactic constructs for blocks. */

  syntax AExp  ::= Int | Id | String
                 | "++" Id
                 | "read" "(" ")"
                 > AExp "/" AExp              [left, strict, division]
                 > AExp "+" AExp              [left, strict, addition]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
				 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"  [strict]
                 | "halt" ";"
                 > "spawn" Stmt
                 > Stmt Stmt                  [left]

  syntax Ids   ::= List{Id,","}               [strict]
  syntax AExps ::= List{AExp,","}             [strict]
endmodule


module IMP
  imports IMP-SYNTAX
/*@ \section{Semantics}
We next give the semantics of IMP++\@.  We start by first defining its
configuration. */

/*@ \subsection{Configuration}
The original configuration of IMP has been extended to include
all the various additional cells needed for IMP++\@.
To facilitate the semantics of threads, more specifically
to naturally give them access to their parent's variables, we prefer a
(rather conventional) split of the program state into an
{\em environment} and a {\em store}.  An environment maps
variable names into {\em locations}, while a store maps locations
into values.  Stores are also sometimes called ``states'', or
``heaps'', or ``memory'', in the literature.  Like values, locations
can be anything.  For simplicity, here we assume they are natural
numbers.  Moreover, each thread has its own environment, so it knows
where all the variables that it has access to are located in the store
(that includes its locally declared variables as well as the variables
of its parent thread).  The store is shared by all threads.  For
simplicity, we assume a sequentially consistent memory model in
IMP++\@.  Note that the \textsf{thread} cell has multiplicity ``*'',
meaning that there could be zero, one, or more instances of that cell
in the configuration at any given time.  This multiplicity information
is important for \K's {\em configuration abstraction} process: it tells
\K how to complete rules which, in order to increase the modularity of the
definition, choose to not mention the entire configuration context.
The \textsf{in} and \textsf{out} cells hold the input and the output
buffers as lists of items. */

  configuration <T color="yellow">
                  <threads color="orange">
                    <thread multiplicity="*" color="blue">
                      <k color="green"> $PGM:Stmt </k>
                      <env color="LightSkyBlue"> .Map </env>
                    </thread>
                  </threads>
                  <br/>
                  <store color="red"> .Map </store>
//                  <in color="magenta"> .List </in>
//                  <out color="Orchid"> .List </out>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
                </T>
// Replace the <in/> and <out/> cells with the next two in order to
// initialize the input buffer through krun
//     <in color="magenta"> $IN:List </in>
//     <out color="Orchid"> .List </out>
// Replace the <in/> and <out/> cells with the next two to connect the
// input/output buffers to stdin/stdout through krun
//     <in color="magenta" stream="stdin"> .List </in>
//     <out color="Orchid" stream="stdout"> .List </out>
// Replace the <in/> and <out/> cells with the next two to connect the
// input/output buffers to stdin/stdout and also allow input through krun
//     <in color="magenta" stream="stdin"> $IN:List </in>
//     <out color="Orchid" stream="stdout"> .List </out>

/*@ We can also use configuration variables to initialize
the configuration through \texttt{krun}.  For example, we may want to
pass a few list items in the \textsf{in} cell when the program makes
use of \texttt{read()}, so that the semantics does not get stuck.
Recall from IMP that configuration variables start with a \textit{\$}
character when used in the configuration (see, for example,
\textit{\$PGM}) and can be initialized with any string by
\texttt{krun}; or course, the string should parse to a term of the
corresponding sort, otherwise errors will be generated.
Moreover, \K allows you to connect list cells to the standard input or
the standard output.  For example, if you add the attribute
\texttt{stream="stdin"} to the \textsf{in} cell, then \texttt{krun}
will prompt the user to pass input when the \textsf{in} cell is empty
and any semantic rule needs at least one item to be present there in
order to match.  Similarly but dually, if you add the attribute
\texttt{stream="stdout"} to the \textsf{out} cell, then any item
placed into this cell by any rule will be promptly sent to the
standard output.  This way, \textsf{krun} can be used to obtain
interactive interpreters based directly on the \K semantics of the
language.  For example:
\begin{verbatim}
bash$ krun programs/sum-3.imppp --no-config
Add numbers up to (<= 0 to quit)? 10
Sum = 55
Add numbers up to (<= 0 to quit)? 1000
Sum = 500500
Add numbers up to (<= 0 to quit)? 0
bash$ 
\end{verbatim}
The option \texttt{-\,\!-no-config} instructs \texttt{krun} to not
display the resulting configuration after the program executes.  The
input/output streaming works with or without this option, although
if you don't use the option then a configuration with empty
\textsf{in} and \textsf{out} cells will be displayed after the program
is executed.  You can also initialize the configuration using
configuration variables and stream the contents of the cells to
standard input/output at the same time.  For example, if you use a
configuration variable in the \textsf{in} cell and pass contents to it
through \texttt{krun}, then that contents will be first consumed and
then the user will be prompted to introduce additional input if the
program's execution encounters more \texttt{read()} constructs. */

/*@ \subsection{The old IMP constructs}
The semantics of the old IMP constructs is almost identical to their
semantics in the original IMP language, except for those constructs
making use of the program state.  Indeed, the rules for variable
lookup and assignment in IMP accessed the \textsf{state} cell, but
that cell is not available in IMP++ anymore.  Instead, we have to use the
combination of environment and store cells.  Thanks to \K's implicit
configuration abstraction, we do not have to mention the
\textsf{thread} and \textsf{threads} cells: these are automatically
inferred (and added by the \K tool at compile time) from the
definition of the configuration above, as there is only one correct
way to complete the configuration context of these rules in order to
match the configuration declared above. In our case here, ``correct way''
means that the \textsf{k} and \textsf{env} cells will be considered as
being part of the same \textsf{thread} cell, as opposed to each being part
of a different thread.  Configuration abstraction is crucial for modularity,
because it gives us the possibility to write our definitions in a way that
may not require us to revisit existing rules when we change the configuration.
Changes in the configuration are quite frequent in practice, typically
needed in order to accommodate new language features.  For example,
imagine that we initially did not have threads in IMP++\@.  There
would be no need for the \textsf{thread} and \textsf{threads} cells in
the configuration then, the cells \textsf{k} and \textsf{env} being simply
placed at the top level in the \textsf{T} cell, together with the
already existing cells.  Then the rules below would be exactly the
same.  Thus, configuration abstraction allows you to not have to
modify your rules when you make structural changes in your language
configuration.

Below we list the semantics of the old IMP constructs, referring the
reader to the \K semantics of IMP for their meaning.  Like we tagged the
addition and the division rules above in the syntax, we also tag the lookup
and the assignment rules below (with tags \texttt{lookup} and
\texttt{assignment}), because we want to refer to them when we generate the
language model (with the \texttt{kompile} tool), basically to allow them to
generate (possibly non-deterministic) transitions.  Indeed, these two rules,
unlike the other rules corresponding to old IMP constructs, can yield
non-deterministic behaviors when more threads are executed concurrently.
In terms of rewriting, these two rules can ``compete'' with each other on
some program configurations, in the sense that they can both match at the
same time and different behaviors may be obtained depending upon which of
them is chosen first. */

  syntax KResult ::= Int | Bool

//@ \subsubsection{Variable lookup}

  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>  [lookup]

//@ \subsubsection{Arithmetic constructs}

  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2

//@ \subsubsection{Boolean constructs}

  rule I1:Int <= I2:Int => I1 <=Int I2
  rule ! T:Bool => notBool T
  rule true && B => B
  rule false && _ => false

/*@ \subsubsection{Empty block}
Non-empty block needs a different semantics, so we move it below
with the semantics of the new IMP++ constructs. */

  rule {} => .   [structural]

//@ \subsubsection{Variable assignment}

  rule <k> X = I:Int; => . ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>  [assignment]

//@ \subsubsection{Sequential composition}

  rule S1 S2 => S1 ~> S2  [structural]

//@ \subsubsection{Conditional statement}

  rule if (true)  S else _ => S
  rule if (false) _ else S => S

//@ \subsubsection{While loop}

  rule while (B) S => if (B) {S while (B) S} else {}  [structural]

/*@ \subsection{The new IMP++ constructs}
We next discuss the semantics of the new IMP++ constructs. */

/*@ \subsubsection{Strings}
First, we have to state that strings are also results.
Second, we give the semantics of IMP++ string concatenation (which
uses the already existing addition symbol \texttt{+} from IMP) by
reduction to the built-in string concatenation operation. */

  syntax KResult ::= String
  rule Str1:String + Str2:String => Str1 +String Str2

/*@ \subsubsection{Variable increment}
Like variable lookup, this is also a supercool transition: we want it
to count both in the non-determinism due to strict operations above it
in the computation and in the non-determinism due to thread
interleavings.  This rule also relies on \K's configuration
abstraction. Without abstraction, you would have to also include the
\textsf{thread} and \textsf{threads} cells. */

  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [increment]

/*@ \subsubsection{Read}
The \texttt{read()} construct evaluates to the first integer in the
input buffer, which it consumes.  Note that this rule is tagged
\texttt{increment}.  This is because we will include it in the set of
potentially non-deterministic transitions when we kompile the definition;
we want to do that because two or more threads can ``compete'' on
reading the next integer from the input buffer, and different choices
for the next transition can lead to different behaviors. */

  rule <k> read() => I ...</k>
       <in> ListItem(I:Int) => . ...</in>  [read]

/*@ \subsubsection{Print}
The \texttt{print} statement is strict, so all its arguments are
eventually evaluated (recall that \texttt{print} is variadic).  We
append each of its evaluated arguments, in order, to the output buffer,
and structurally discard the residual \texttt{print} statement with an
empty list of arguments.  We only want to allow printing integers and
strings, so we define a {\em Printable} syntactic category including
only these and define the \texttt{print} statement to only print
{\em Printable} elements.  Alternatively, we could have had two
similar rules, one for integers and one for strings.  Recall that,
currently, \K's lists are cons-lists, so we cannot simply rewrite the
head of a list ($P$) into a list ($\kdot$).  The first rule below is tagged,
because we want to include it in the list of transitions when we kompile;
different threads may compete on the output buffer and we want to capture
all behaviors.  The second rule is structural because we do not want it to
count as a computational step. */

  syntax Printable ::= Int | String
  rule <k> print(P:Printable,AEs:AExps => AEs); ...</k>
       <out>... . => ListItem(P) </out>  [print]
  rule print(.AExps); => .  [structural]

/*@ \subsubsection{Halt}
The \texttt{halt} statement empties the computation, so the rewriting process
simply terminates as if the program terminated normally.  Interestingly, once
we add threads to the language, the \texttt{halt} statement as defined below
will terminate the current thread only.  If you want an abrupt termination
statement that halts the entire program, then you need to discard the entire
contents of the \textsf{threads} cell, so the entire computation abruptly
terminates the entire program, no matter how many concurrent threads it has,
because there is nothing else to rewrite.  */

  rule <k> halt; ~> _ => . </k>
  
/*@ \subsubsection{Spawn thread}
A spawned thread is passed its parent's environment at creation time.
The \texttt{spawn} statement in the parent thread is immediately
dissolved so the parent thread can continue its execution.  We only
consider a sequentially consistent shared memory model for IMP++, but
other memory models can also be defined in \K; see, for example, the
definition of KERNELC\@.  Note that the rule below does not need to be
tagged in order to make it a transition when we kompile, because the creation
of the thread itself does not interfere with the execution of other threads.
Also, note that \K's configuration abstraction is at heavy work here, in two
different places.  First, the parent thread's \textsf{k} and \textsf{env} cells
are wrapped within a \textsf{thread} cell.  Second, the child thread's
\textsf{k} and \textsf{env} cells are also wrapped within a \textsf{thread}
cell.  Why that way and not putting all these four cells together within the
same thread, or even create an additional \textsf{threads} cell at top
holding a \textsf{thread} cell with the new \textsf{k} and
\textsf{env}?  Because in the original configuration we declared
the multiplicity of the \textsf{thread} cell to be ``$*$'', which
effectively tells the \K tool that zero, one or more such cells can
co-exist in a configuration at any moment.  The other cells have the
default multiplicity ``one'', so they are not allowed to multiply.
Thus, the only way to complete the rule below in a way consistent with
the declared configuration is to wrap the first two cells in a
\textsf{thread} cell, and the latter two cells under the ``$\kdot$''
also in a \textsf{thread} cell.  Once the rule applies, the spawning
thread cell will add a new thread cell next to it, which is consistent
with the declared configuration cell multiplicity. */

  rule <k> spawn S => . ...</k> <env> Rho </env>
       (. => <thread>... <k> S </k> <env> Rho </env> ...</thread>)

/*@ \subsubsection{Terminate thread}
When the computation of a thread is empty, the thread is dissolved.
This rule can be regarded as a configuration cleanup operation, so it
needs not count as a computational step; we therefore tag it structural. */

  rule <thread>... <k> . </k> ...</thread> => .  [structural]

/*@ \subsubsection{Nonempty Blocks}
The body statement of a non-empty block is executed normally, making sure
that the environment at the block entry point is saved in the computation,
in order to be recovered after the block body statement.  This step is
necessary because blocks can declare new variables having the same
name as variables which already exist in the environment, and our
semantics of variable declarations is to update the environment map in
the declared variable with a fresh location.  Thus, variables which
are shadowed lose their original binding, which is why we take a
snapshot of the environment at block entrance and place it after the
block body (see the semantics of environment recovery at the end of
this module).  Note that any store updates through variables which are
not declared locally are kept at the end of the block, since the store
is not saved/restored.  An alternative to this environment save/restore
approach is to actually maintain a stack of environments and to push a
new layer at block entrance and pop it at block exit.  The variable
lookup/assign/increment operations then also need to change, so we do
not prefer that non-modular approach. Compilers solve this problem by
statically renaming all local variables into fresh ones, to
completely eliminate shadowing and thus environment
saving/restoring.  The second rule below can also be structural,
because what it effectively does is to take a snapshot of the current
environment; this operation is arguably not a computational step. */

  rule <k> {S} => S ~> env(Rho) ...</k> <env> Rho </env>  [structural]

/*@ \subsubsection{Variable declaration}
We allocate a fresh location for each newly declared variable and
initialize it with 0. */

  rule <k> int (X:Id,Xs:Ids => Xs); ...</k>
       <env> Rho:Map => Rho[N/X] </env>
       <store>... . => N|->0 ...</store>
    when fresh(N:Nat)
  rule int .Ids; => .  [structural]

/*@ \subsubsection{Auxiliary operations}
We only have one auxiliary operation in IMP++, the environment
recovery.  Its role is to discard the current environment in the
\textsf{env} cell and replace it with the environment that it holds.
This rule is structural: we do not want them to count as computational
steps in the transition system of a program. */

  syntax K ::= env(Map)
  rule <k> env(Rho) => . ...</k> <env> _ => Rho </env>    [structural]

/*@ If you want to avoid useless environment recovery steps and keep the size
of the computation structure smaller, then you can also add the rule
\begin{verbatim}
 rule (env(_) => .) ~> env(_)  [structural]
\end{verbatim}
This rule acts like a ``tail recursion'' optimization, but for blocks. */
endmodule

/*@ \section{On Kompilation Options}

We are done with the IMP++ semantics.  The next step is to kompile the
definition using the \texttt{kompile} tool, this way generating a language
model.  Depending upon for what you want to use the generated language model,
you may need to kompile the definition using various options.  We here discuss
these options.

To tell the \K tool to exhaustively explore all the behaviors due to the
non-determinism of addition, division, and threads, we have to kompile
with the command:
\begin{verbatim}
kompile imp.k --superheat="addition division" --supercool="lookup increment"
              --transition="lookup assignment increment read print"
\end{verbatim}
As already mentioned, the syntax and rule tags play no theoretical or
foundational role in \K.  They are only a means to allow \texttt{kompile} to
refer to them in its options, like we did above.  By default, \texttt{kompile}'s
options are all empty, because this yields the fastest language model when
executed.  Nonempty options may slow down the execution, but they instrument
the language model to allow for formal analysis of program behaviors, even for
exhaustive analysis.

Theoretically, the heating/cooling rules in \K are fully reversible and
unconstrained by side conditions as we showed in the semantics of IMP\@.
For example, the theoretical heating/cooling rules corresponding to the
\texttt{strict} attribute of division are the following:
$$
\begin{array}{l}
E_1 \texttt{/} E_2 \ \ \Rightarrow \ \ E_1 \kra \square \texttt{/} E_2 \\
E_1 \kra \square \texttt{/} E_2 \ \ \Rightarrow \ \ E_1 \texttt{/} E_2 \\
E_1 \texttt{/} E_2 \ \ \Rightarrow \ \ E_2 \kra E_1 \texttt{/} \square \\
E_2 \kra E_1 \texttt{/} \square \ \ \Rightarrow \ \ E_1 \texttt{/} E_2
\end{array}
$$
The other semantic rules apply {\em modulo} such structural rules.
For example, using heating rules we can bring a redex (a subterm which
can be reduced with semantic rules) to the front of the computation,
then reduce it, then use cooling rules to reconstruct a term over the
original syntax of the language, then heat again and
non-deterministically pick another redex, and so on and so forth
without losing any opportunities to apply semantic rules.
Nevertheless, these unrestricted heating/cooling rules may create an
immense, often unfeasibly large space of possibilities to analyze.
Super-heating/cooling implement an optimization which works well with
other implementation choices made in the current \K tool.  Recall from
the detailed description of the IMP language semantics that
(theoretical) reversible rules like above are restricted to complementary
conditional rules of the form
$$
\begin{array}{l}
E_1 \texttt{/} E_2 \ \ \Rightarrow \ \ E_1 \kra \square \texttt{/} E_2
\ \ \textsf{if} \ \ E_1\not\in\KResult \\
E_1 \kra \square \texttt{/} E_2 \ \ \Rightarrow \ \ E_1 \texttt{/} E_2
\ \ \textsf{if} \ \ E_1\in\KResult \\
E_1 \texttt{/} E_2 \ \ \Rightarrow \ \ E_2 \kra E_1 \texttt{/} \square
\ \ \textsf{if} \ \ E_2 \not\in\KResult \\
E_2 \kra E_1 \texttt{/} \square \ \ \Rightarrow \ \ E_1 \texttt{/} E_2
\ \ \textsf{if} \ \ E_2 \in \KResult
\end{array}
$$
Therefore, our tool eagerly heats and lazily cools the computation.
In other words, heating rules apply until a redex gets placed on the
top of the computation, then some semantic rule applies and rewrites
that into a result, then a cooling rule is applied to plug the
obtained result back into its context, then another argument may be
chosen and completely heated, and so on.  This leads to efficient
execution, but it may and typically does hide program behaviors.
Super-heating/cooling allows you to interfere with this process.
More precisely, whenever a rule tag is included in the \texttt{supercool}
category, the \K tool will continue to apply (unrestricted) cooling rules
on the resulting computation disregarding the membership to $\KResult$
side condition, thus plugging everything back into its context, until no
construct tagged \texttt{superheat} is left uncooled.  This way, the
heating rules now have the possibility to pick another evaluation order
for the cooled fragment of computation.  This way, we can think of
super-heating/cooling as marking fragments of computation in which
exhaustive analysis of the evaluation order is performed.  Used carefully,
this mechanism allows us to explore more non-deterministic behaviors of a
program, even all of them like here, still efficiently.  For example, with
the semantics of IMP++ given below, the \texttt{krun} command with the
\texttt{-\,\!-search} option detects all five behaviors of the
following IMP++ program (\texttt{x} can be 0, 1, 2, 3, or undefined
due to division-by-zero):
\begin{verbatim}
  int x,y;
  x = 1;
  y = ++x / (++x / x);
\end{verbatim}

Besides non-determinism due to underspecified argument evaluation
orders, which the current \K tool addresses by means of superheating
and supercooling as explained above, there is another important source
of non-determinism in programming languages: non-determinism due to
concurrency/parallelism.  For example, when two or more threads are
about to access the same location in the store and at least one of
these accesses is a write (i.e., an instance of the variable
assignment rule), there is a high chance that different choices for
the next transition lead to different program behaviors.  While in the
theory of \K all the non-structural rules count as computational steps
and hereby as transitions in the transition system associated to the
program, in practice that may yield a tremendous number of step
interleavings to consider.  Most of these interleavings are behaviorally
equivalent for most purposes.  For example, the fact that a thread computes
a step $8\texttt{+}3 \Rightarrow 11$ is likely irrelevant for the other
threads, so one may not want to consider it as an observable transition in
the space of interleavings.  Since the K tool cannot know without help which
transitions need to be explored and which do not, our approach is to
let the user say so explicitly using the \texttt{transition} option of
\texttt{kompile}. */
