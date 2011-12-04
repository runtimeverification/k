module IMPPP-SYNTAX
/*@ \section{Syntax}
IMP++ adds several syntactic constructs to IMP.  Also, since the
variable declaration construct is generalized to be used anywhere a
statement can be used, not only at the beginning of the program, we
need to remove the previous global variable declaration of IMP and
instead add a variable declaration statement construct. */

/*@ \subsection{The old IMP constructs}
The following constructs are taken over from IMP.  For execution
purposes, we add the ``superheat'' attribute to addition and division.
This attribute has no theoretical significance, in that it does not
affect the semantics of the language in any way.  It only has
practical relevance, specific to our implementation of the \K tool.
Specifically, it tells the tool that the ``\verb|--search|'' option
should exhaustively explore all the non-deterministic behaviors due to
the strictness of the corresponding language construct.  Without it,
for performance reasons the \K tool chooses an arbitrary but fixed
order to evaluate the arguments of the strict language construct, thus
losing behaviors due to missed interleavings.  This aspect was
irrelevant in IMP, because its expressions had no side effects, but it
becomes relevant in IMP++.  Note that the ``superheat'' attribute
pairs with corresponding ``supercool'' attributes of rules (see the
variable lookup and increment rules below).  These two attributes
together tell the \K tool to exhaustively explore the space of
interleavings between the supercool and the superheat points. */

  syntax AExp ::= #Id | #Int
                | AExp "+" AExp    [:prec(33) gather (E e) superheat strict:]
                | AExp "/" AExp    [:prec(31) gather (E e) superheat strict:]
  syntax BExp ::= #Bool
                | AExp "<=" AExp   [:prec(37) seqstrict latex("{#1}\leq{#2}"):]
                | "not" BExp       [:prec(53) strict:]
                | BExp "and" BExp  [:prec(55) strict(1):]
  syntax Stmt ::= "skip"
                | #Id ":=" AExp    [:prec(80) strict(2):]
                | Stmt ";" Stmt    [:prec(100) gather(e E):]
                | "if" BExp
                  "then" Stmt
                  "else" Stmt      [:prec(85) strict(1):]
                | "while" BExp
                  "do" Stmt        [:prec(85):]
  syntax Ids ::= List{#Id,","}

/*@ \subsection{The new IMP++ constructs}
The syntax of the new IMP++ constructs is self-explanatory.
Note that \texttt{print} is variadic, taking a list of expressions as
argument.  It is also strict, which means that the entire list of
expressions, that is, each expression in the list, will be evaluated. */

  syntax AExp ::= #String
                | "++" #Id               [:prec(0):]
                | "read" "(" ")"
  syntax AExps ::= List{AExp,","}

  syntax Stmt ::= "print" "(" AExps ")"  [:strict:]
                | "halt"
                | "spawn" Stmt           [:prec(90):]
                | "{" "}"
                | "{" Stmt "}"           [:gather(&):]
                | "var" Ids              [:prec(70):]
end module



module IMPPP
  imports IMPPP-SYNTAX
/*@ \section{Semantics}
We next give the semantics of IMP++.  We start by first defining its
configuration, then we give the semantics of all the constructs
borrowed from IMP, and finally the semantics of the new IMP++
constructs.  To facilitate the semantics of threads, more specifically
to naturally give them access to their parent's variables, we prefer a
(rather conventional) semantics based on a split of the program state
into an {\em environment} and a {\em store}.  An environment maps
variable names into {\em locations}, while a store maps locations
into values.  Stores are also sometimes called ``states'', or
``heaps'', or ``memory'', in the literature.  Like values, locations
can be anything.  For simplicity, here we assume they are natural
numbers. */

/*@ \subsection{Configuration}
The original configuration of IMP has been extended to include
all the various additional cells needed for IMP++.  As explained
above, the IMP state is now split into environment and a store.
Moreover, each thread has its own environment, so it knows where all
the variables that it has access to (that includes its locally
declared variables as well as the variables of its parent thread) are
located in the store.  The stored is shared by all threads.  Note that
the \textsf{thread} cell has multiplicity ``*'', meaning that there
could be zero, one or more instances of that cell in the configuration
at any given time; this multiplicity information is irrelevant here,
but it is important in more complex languages (see, e.g., SIMPLE).
The \textsf{nextLoc} cell holds the next available location in the
store and is needed for the semantics of variable declarations.
Finally, the \textsf{in} and \textsf{out} cells hold the input and the
output buffers, as list of items.  The configuration variable
{\em \$IN} has no semantic meaning; it is a means for the user to pass
initial values into the configuration using the \K tool (see example
programs, both of IMP and IMP++).  */

  configuration
    <T color="yellow">
      <threads color="orange">
        <thread multiplicity="*" color="red">
          <k color="green"> $PGM:Stmt </k>
          <env color="LightSkyBlue"> .Map </env>
        </thread>
     </threads>
     <br/>
     <store color="white"> .Map </store>
     <nextLoc color="gray"> 0 </nextLoc>
//     <in color="magenta"> $IN:List </in>
//     <out color="Orchid"> .List </out>
     <in color="magenta" stream="stdin"> $IN:List </in>
     <out color="Orchid" stream="stdout"> .List </out>
    </T>

/*@ \subsection{The old IMP constructs}
The semantics of the old IMP constructs is almost identical to their
semantics in the original IMP language, except for those constructs
making use of the program state.  Indeed, the rules for variable
lookup and assignment in IMP accessed the \textsf{state} cell, but
that cell is not available in IMP++ anymore.  Instead, we have to use the
combination of environment and store cells.  Thanks to \K's implicit
configuration abstraction, we do not have to mention the
\textsf{thread} and \textsf{threads} cells: these are automatically
inferred (and added by the \K tool) from the definition of the
configuration above.  Configuration abstraction is crucial for
modularity: we do not need to revisit the existing rules when we
change the configuration (changes in the configuration are needed,
e.g., to accommodate new language features).  As explained above when
we discussed the ``superheat'' attribute to syntactic constructs, we
annotate the variable lookup rule with the attribute ``supercool''.
This effectively tells the \K tool to exhaustively explore all the
behaviors due to the non-determinism of addition and division.

The superheating and supercooling attributes/tags to syntactic
constructs and rules therefore allow us to more effectively use the \K
tool to explore the program non-determinism due to unspecified orders
of argument evaluation for strict language constructs.  There is
another important source of non-determinism in programming languages,
namely non-determinism due to concurrency.  For example, when two or
more threads are about to access the same location in the store and at
least one of these accesses is a write (i.e., an instance of the
variable assignment rule), there is a high chance that different
choices for the next transition lead to different program behaviors.
While in theory all the non-structural rules count as computational
steps and hereby as transitions in the transition system (or Kripke
structure) associated to the program, in practice that may yield a
tremendous number of step interleavings to consider.  Most of these
interleavings are behaviorally equivalent for most purposes.  For
example, the fact that a thread computes a step $8\texttt{+}3
\Rightarrow 11$ is likely irrelevant for the other threads, so one may
not want to consider it as an observable transition in the space of
interleavings.  Since the \K tool cannot know which transitions need
to be explored and which do not, its approach to let the user say it
explicitly.  The rules tagged with ``transition'', like the variable
lookup and assignment rules below, are the only ones considered when
exploring a program's state space (with search or model-checking).

Below we list the semantics of the old IMP constructs, referring the
reader to the \K semantics of IMP for their meaning.  */

// Values and results

  syntax Val ::= #Int | #Bool
  syntax AExp ::= Val
  syntax KResult ::= Val

// Variable lookup

  rule <k> X:#Id => I ...</k>
       <env>... X |-> N:#Nat ...</env>
       <store>... N |-> I:#Int ...</store>  [:supercool transition:]

// Arithmetic constructs

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0

// Boolean constructs

  rule I1 <= I2 => I1 <=Int I2
  rule not T:#Bool => notBool T
  rule true and B:BExp => B
  rule false and B => false

// Skip

  rule skip => .

// Variable assignment

  rule <k> X := I => . ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store> [transition]

// Sequential composition

  rule S1:Stmt ; S2:Stmt => S1 ~> S2 [structural]

// Conditional

  rule if  true then S1 else _  => S1
  rule if false then _  else S2 => S2

// While loop

  rule <k> while B do S:Stmt => if B then S ; while B do S else {} ...</k>

/*@ \subsection{The new IMP++ constructs}
We next discuss the semantics of the new IMP++ constructs. */

/*@ \subsubsection{Strings}
First, we have to state that strings are also values.
Second, we give the semantics of IMP++ string concatenation (which
uses the already existing addition symbol \texttt{+} from IMP) by
reduction to the builtin string concatenation operation. */

  syntax Val ::= #String
  rule Str1:#String + Str2:#String => Str1 +String Str2

/*@ \subsubsection{Variable increment}
Like variable lookup, this is also a supercool transition: we want it
to count both in the non-determinism due to strict operations above it
in the computation and in the non-determinism due to thread interleavings. */

  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [:supercool transition:]

/*@ \subsubsection{Read}
The \texttt{read()} construct evaluates to the first integer in the
input buffer, which it consumes.  Note that this rule is tagged as
transition.  This is because two or more threads can ``compete'' on
reading the next integer from the input buffer, and different choices
for the next transition can lead to different behaviors. */

  rule <k> read() => I ...</k>
       <in> ListItem(I) => . ...</in>  [:transition:]

/*@ \subsubsection{Print}
The \texttt{print} statement was strict, so all its arguments are now
evaluated (recall that \texttt{print} is variadic).  We append each of
its evaluated arguments to the output buffer, and structurally discard
the residual \texttt{print} statement with an empty list of
arguments.  This rule is also a transition, because different threads
may compete on the output buffer; we want to capture all behaviors. */

  syntax Vals ::= List{Val,","}
  rule <k> print(V:Val,Vs:Vals => Vs) ...</k>
       <out>... . => ListItem(V) </out>  [:transition:]
  rule print(.Vals) => .                 [:structural:]

/*@ \subsubsection{Halt}
The \texttt{halt} statement discards the entire contents of the
\textsf{threads} cell, so the computation abruptly terminates because
there is nothing else to rewrite.  Thus, our semantics of
\texttt{halt} here is to abruptly terminate the entire program.
We keep the (empty) \textsf{threads} cell because we want the final
configuration to have the same structure regardless of whether the
program terminated abruptly or not. */

  rule <threads>... <k> halt ...</k> ...</threads>
    => <threads> .Bag </threads>

/*@ \subsubsection{Spawn thread}
A spawned thread is passed its parent's environment at creation time.
The \texttt{spawn} statement in the parent thread is immediately
dissolved so the parent thread can continue its execution.  Note that
the rule below does not need to be tagged as a transition, because the
creation of the thread itself does not interfere with the execution of
other threads. */

  rule <k> spawn S => . ...</k>
       <env> Rho </env>
       (. => <thread>... <k> S </k> <env> Rho </env> ...</thread>)

/*@ \subsubsection{Terminate thread}
When the computation of a thread is empty, the thread is dissolved.
This rule can be regarded as a configuration cleanup operation, so it
needs not count as a computational step; we therefore tag it structural. */

  rule <thread>... <k> .K </k> ...</thread> => .  [:structural:]

/*@ \subsubsection{Blocks}
Empty blocks dissolve, like the \texttt{skip} statement of IMP.  For
demonstration purposes, we tag it as a structural rule.  The body
statement of a non-empty block is executed normally, making sure that
the environment at the block entry point is saved in the computation
to be recovered after the block body statement.  This is necessary
because blocks can declare new variables, thus destroying the original
environment.  This rule can also be structural, because what it
effectively does is to take a snapshot of the current environment;
this operation is arguably not a computational step. */

  rule {} => .                           [:structural:]
  rule <k> {S} => S ~> env(Rho) ...</k>
       <env> Rho:Map </env>              [:structural:]

/*@ \subsubsection{Variable declaration}
We allocate a new location for each newly declared variable and
initialize it with 0, without worrying about memory reuse. */

  rule <k> var (X,Xl => Xl:Ids) ...</k>
       <env> Rho => Rho[N/X] </env>
       <store>... . => N |-> 0 ...</store>
       <nextLoc> N => N +Int 1 </nextLoc>
  rule var .Ids => .                        [:structural:]

/*@ \subsubsection{Auxiliary operations}
We only have one auxiliary operation in IMP++, the environment
recovery.  Its role is to discard the current environment in the
\textsf{env} cell and replace it with the environment that it holds.
The first rule below is an optimization, to avoid useless environment
recovery steps and keep the size of the computation structure smaller
(like a ``tail recursion'' optimization, but for blocks).  Both rules
are structural, because we do not want them to count as computational
steps in the transition system of a program. */

  syntax K ::= env Map
  rule (env(_) => .) ~> env(_)                         [:structural:]
  rule <k> env(Rho) => . ...</k> <env> _ => Rho </env> [:structural:]

end module
