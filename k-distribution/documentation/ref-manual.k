// Copyright (c) 2013-2015 K Team. All Rights Reserved.
/*!
\setlength{\parindent}{1em}
\title{\K Reference Manual}
\author{\K Team}
\organization{University of Illinois at Urbana-Champaign, USA\\ Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\KTool}{\K tool\xspace}
\newcommand{\krun}{\texttt{krun}\xspace}
\newcommand{\kast}{\texttt{kast}\xspace}
\newcommand{\kompile}{\texttt{kompile}\xspace}
\newcommand{\bluetext}[1]{\textcolor{blue}{\it #1\\}}
\newcommand{\alert}[1]{\textcolor{red}{\it #1\\}}


\titleformat{\section}{\bfseries}{\thesection.}{1em}{}
\titleformat{\subsection}{\bfseries}{\thesubsection.}{1em}{}
\titleformat{\subsubsection}{\bfseries}{\thesubsubsection.}{1em}{}
\titleformat{\paragraph}{\bfseries}{\theparagraph.}{1em}{}
\titlespacing{\section}{0pt}{12pt}{6pt}
\titlespacing{\subsection}{0pt}{12pt}{6pt}
\titlespacing{\subsubsection}{0pt}{12pt}{6pt}
\titlespacing{\paragraph}{0pt}{12pt}{6pt}
*/


//@ \alert{This document is a work in progress. Any feedback will be appreciated.}



/*@

\section{Introduction}

\bluetext{The goal of the manual, how should it be used, what should it be read before. (Grigore, Dorel)}

*/

/*@
\section{\K Definitions}

*/

/*@
\subsection{Syntax of Defined Languages}

\bluetext{(Radu)}

\subsubsection{BNF-like Syntax}

Tokenizer/Lexer rules

K has predefined the lexer rules for the most common syntactic categories that are directly accessible through subsorting:
\begin{verbatim}
syntax #Bool   ::= Token{"true"} | Token{"false"}
syntax #Id     ::= Token{[a-zA-Z][a-zA-Z0-9]*}
syntax #Int    ::= Token{[\-\+]? [0-9]+}
syntax #String ::= Lexer{"\"" (~[\"\\] | "\\\"" | "\\")* "\""}
                   // where '\' cannot be followed by double quote
syntax #Float  ::= Lexer{[0-9]+ "." [0-9]+ ([eE] #Int)}
syntax #Float  -/- [a-zA-Z0-9\.]
\end{verbatim}

For some languages these may not be enough so you might want to declare your
own.  There are two main things that you have to consider: the regular
expression that will do the matching, and the follow restriction. The latter
tells the regular expression when not to stop matching.

A regular expression for the matcher is similar to the one in SDF. Basically
you may write strings, sets of tokens (using [...]), add optional arguments
with '?'. You can negate a set of tokens by prefixing it with '\texttildelow'.
Inside a character set you may write individual characters or entire ranges:
a-z A-Z 0-9. Anything other than these need to be escaped using backslash.

The follow restriction is an important feature of the SDF parser, as the
lexical rules are not greedy by default. The last line in the example above,
says that \#Float cannot be followed by one of the characters in the set. The
list can be extended to check multiple characters ahead by concatenating sets
with '.' (\verb^syntax X -/- [a].[b].[c]^).

Sometimes you may also want to specify follow restrictions for keywords to
avoid some ambiguities:

\verb^syntax "keyword" -/- [a-zA-Z0-9]^

Another useful construction is a list separated by a character. For example the
name of a module in K is matched by a construction like the following:

\begin{verbatim}
syntax MODNAME ::= Lexer{"#"?{[a-z0-9A-Z\_]+ "-"}+}
syntax MODNAME -/- [a-z0-9A-Z\-\_]
\end{verbatim}

The construction \{<char set> "<separator>"\}+ will match 'A', 'A-A', 'A-A-A',
but not 'A-'.

\verb^Lexer{...}^ and \verb^-/-^ are the main way of specifying a lexical rule,
but if your expression is simple enough, you may write directly
\verb^Token{...}^. This will try to infer automatically the follow restriction
(if needed). Looking back at the rule for \#Id, it will be equivalent to:

\begin{verbatim}
syntax #Id ::= Lexer{[a-zA-Z][a-zA-Z0-9]*}
syntax #Id -/- [a-zA-Z0-9]
\end{verbatim}

Note that this works for simple expressions that have a repeated character set
at the end. If you want to specify something more complex, you will have to use
\verb^Lexer{...}^ and specify the follow restriction.



\subsubsection{Disambiguation Mechanisms}

\bluetext{Filters, priorities, associativity etc}

\subsubsection{Lists}


\subsubsection{Syntax-Specific Tags}

\bluetext{strict, klabel, only-label, klatex, \dots}

*/

/*@
\subsection{\K Abstract Syntax Trees}
\bluetext{Definition, syntax, how the ASTs are automatically generated from the syntax, interaction with specific tags from the syntax, \ldots (Grigore, Traian, Radu, Dorel)}
*/

/*@
\subsection{Configurations}
\label{sec:configurations}
\bluetext{Syntax, specific attributes with the focus on "stream", special variables (e.g., \$PGM), how the initial configuration is generated, \ldots (Radu, Traian, Andrei A)}

*/

/*@
\subsection{Rules}
\bluetext{Syntax, specific tags, the use of ASTs, (Radu, Traian, Andrei A, \ldots)}

*/

/*@

\subsection{Contexts}

\bluetext{(Radu with help from Traian)}
*/

/*@
\subsection{Functions and Predicates}
\alert{Even if the contents of this subsection can be distributed in the previous ones, I think that functions and predicates are important and deserves to be presented into a special subsection.}
\bluetext{Syntax, rules, generated predicates, \ldots (Traian, Dorel)}

*/

/*@
\subsection{Symbolic Calculus Support}
\bluetext{(Andrei S, Andrei A)}

\subsubsection{Fresh Names and Symbolic Expressions}

\subsubsection{Connection to a SMT Solver}

\subsubsection{Theories}

*/

/*@
\section{\KTool}

*/

/*@
\subsection{Compiling \K Definitions --- the \kompile tool}

\bluetext{(Traian, Radu, Andrei A)}
*/

/*@
\subsection{Running Programs with \K Definitions -- the \krun tool}

\bluetext{(Dwight)}

Programs in \K are executed by means of invocation of the \krun tool. In
its simplest possible form, \krun is executed with only a single
command-line argument: the name of the program to be run. However, \krun
also provides a number of command line options designed to allow more
complicated behaviors and ways to specify what to execute. These options can be
viewed by executing the command \verb^krun -h^, and details of each of them
will be provided in the sections below.
*/

/*@
\subsubsection{Specifying the definition to execute with:
\texttt{-{}-k-definition}, \texttt{-{}-compiled-def}}

In order for \krun to be able to execute anything, it needs to be able to
decide where to look for information about the \K semantics it is executing
under. By default, if no options are specified, it looks in the current working
directory for a directory with the suffix ``-kompiled''. If it finds exactly one
of these, it assumes that this contains the compiled semantics you wish to use
to execute. If instead it finds no such directories, or more than one such
directory, it will throw an error.

However, sometimes it is desirable to be able to compile more than one
semantics into the same directory, or to be able to execute a semantics with
\krun from outside the directory the semantics resides in. This is where
the \verb^--k-definition^ and \verb^--compiled-def^ directories come into play.
The simplest way to specify this information is with the \verb^--compiled-def^
flag, which takes a single argument representing the path to the compiled \K
definition's directory. If this directory exists, it assumes it contains the
semantics you wish to execute with, and proceeds accordingly.

The \verb^--k-definition^ flag behaves similarly. However, instead of accepting
the path to the compiled \K definition, it instead accepts as an argument the
path to the main file of extension .k in your semantics (that is to say, the
one you executed \kompile on). It then attempts to infer the location of
the compiled \K definition from this path. Needless to say, if you executed
\kompile with the \verb^--output^ flag, it will not succeed, and will
throw an error message instead. In this case, simply use the
\verb^--compiled-def^ flag instead to specify the path you passed to
\verb^kompile --output^.
*/

/*@
\subsubsection{Specifying the program to execute under the semantics:
\texttt{-{}-pgm}, \texttt{-{}-term}, \texttt{-c}}

In order for a program to be executed by \krun, it needs to know how to
obtain the term representing the configuration it is supposed to rewrite. By
default, this is obtained by means of the configuration declaration in your
definition's semantics, and the abstraction of configuration variables.  By
specifying one or more configuration variables (see section \ref{sec:configurations}
for details), you are able to tell \krun to plug values of your choosing
into the initial configuration.

As a convention, the most common of these is the configuration variable \$PGM.
\$PGM is special because we assume that it is the name of the program or main
piece of syntax you wish to execute in your semantics. As such, it has several
special mechanisms in place to allow you to specify a value for it. The
simplest of these is to specify the name of a file containing your program (or
a different value to be parsed if you have specified an external parser. See
section \ref{sec:external-parsers}) on the command line as an argument. If you do this,
\krun will automatically invoke the parser and return a parsed value to
be put into the \$PGM configuration variable.

You can also specify a value to be parsed for the \$PGM variable with the
\verb^--pgm^ flag. This is just syntactic sugar: the command
\verb^krun --pgm foo^ and the command \verb^krun foo^ are semantically
equivalent.

Finally, you may specify the value for the \$PGM variable the same way values
are specified for all other configuration variables. Since you can specify an
arbitrarily large number of configuration variables in your initial
configuration, it isn't feasible to specify all of them as arguments on the
command line unless they are referenced by name. This is the purpose of the
\verb^krun -c^ flag. This flag takes two arguments: the name of the
configuration variable to be specified, and the value it should contain. For
example, to tell \krun that the program to be executed should be the
lambda calculus identity function, we would construct the command
\verb^krun -cPGM="lambda x . x"^. This pattern can also be used to specify any
other configuration variable by its name and the value you wish it to have.

It's worth noting however that all of these approaches operate under the
assumption that you wish to make use of the configuration variable abstraction
when constructing a term for \krun to rewrite. However, sometimes, for
example when restarting a previously saved computation (See section \ref{sec:kast}),
it is desirable to specify the entire term to be rewritten manually. This is
where the option \verb^--term^ comes in. By specifying a value to the
\verb^--term^ option, the configuration declaration in the semantics is
bypassed entirely, and \krun assumes that the entirety of the term to be
rewritten consists of whatever it parses from the value of the option.
*/

/*@
\subsubsection{Searching the state space of programs:
\texttt{-{}-search}, \texttt{-{}-pattern}, \texttt{-{}-bound}, \texttt{-{}-depth},
\texttt{-{}-graph}}

So far we have been operating on the assumption that all you want to do with
your semantics is execute it. However, the ultimate purpose of the \K tool is
to provide a mechanism for specifying formal semantics of programming languages
so that you can do more complicated types of formal analyses of programs. As
such, the \krun tool provides a number of options designed to assist in the
analysis of programs that you execute. The simplest of these tools is the
ability to search the state space of programs.

In order to make use of the search functionality that \krun provides, it is
first necessary to tune your semantics for nondeterminism by appropriately
specifying values for the \verb^--transition^, \verb^--superheat^, and
\verb^--supercool^ flags to \kompile. For information on how to do this, please
refer to section \ref{sec:nondeterminism}.

Once this is done, the simplest possible entry point into the mechanisms \krun
provides for searching the state space of programs is the \verb^--search^ flag.
By specifying this flag, instead of executing only a single run of the program,
it instead attempts to find all possible final states of that program. That is
to say, it will return a list of all the configurations your program is capable
of terminating in.

Unfortunately, for large programs with significant amounts of nondeterminism,
this may be something which takes too much time. Additionally, you may desire
to write programs which do not terminate, or which otherwise are not feasible
to allow to explore the entire state space of the program to termination. This
is why we provide tools for specifying bounds on the exploration of the state
space which is provided by the search command.

The first of these is the \verb^--bound^ flag. This takes an integer argument
specifying the maximum number of solutions you are looking for. Once it has
found at least as many solutions as you asked for as a bound, the search will
terminate at that point without looking for further solutions.

The second is the \verb^--depth^ flag. \krun operates by performing a
breadth-first search of the state space of the program. As such, one possible
way to limit the resources required to complete an exploration is to put a
maximum limit on the depth of the search. If a depth of N is specified, \krun
will terminate the search as soon as all states that are at most N states away
from the initial configuration have been explored.

By default, the \verb^--search^ command only returns final states: that is to
say, states in which no further rewriting is possible. However, if I wish to
explore only a finite depth of the program, this is likely to be undesirable
behavior. If I specified a depth of 3, and there were no programs which
terminated within three steps, by default the search would return no results.
In order to prevent this, \krun makes use of a number of options it provides to
decide which types of states are considered solutions in order to set some
intelligent defaults.

By default, the \verb^--search^ command returns only final states, unless a
depth parameter is provided, in which case it returns all states beginning with
the initial state and ending with those states at the maximum depth bound away.
If however you wish to specify both a depth parameter and expect the search to
only return final states, this is also possible by replacing the flag
\verb^--search^ with the flag \verb^--search-final^. You may also retrieve all
states even without specifying a depth bound if you use the flag
\verb^--search-all^. Finally, the flags \verb^--search-one-step^ and
\verb^--search-one-or-more-steps^ round out the selection by allowing you to
select only configurations one step away from the initial state, or to select
only configurations at least one step away from the initial state,
respectively.

Sometimes, however, the mechanisms described so far do not provide what you
require in order to be able to select only the states you wish to select. For
this purpose, \krun allows you to specify search patterns with the
\verb^--pattern^ flag. By specifying a \K rule without any rewrites in it (i.e.
a pattern plus an optional side condition and optional attributes), you can
perform matching and check side conditions on the results of the search, and
discard all the solutions which do not meet your search criteria. If the search
pattern contains variables, the search will return a substitution, telling you
the values of each of those variables in the solution you requested. You can
also tell \krun that you don't want to see the value of a particular variable
by using an anonymous variable (i.e. \_) instead of a named variable in your
search pattern.

It is worth noting that the \verb^--pattern^ flag is also able to be used on
normal executions. The effect this has is to execute the program until it
has reached its final configuration, and then perform a search on the resulting
configuration. Therefore, you will either get a single solution containing the
substitution through which the configuration resulting from execution matches
the specified pattern, or else you will get no solutions, indicating that the
configuration resulting from execution does not match the specified pattern.
This may be useful in cases where you want to perform pattern matching on the
result of executing a program, for example if you wish to write a test case
which asserts that all programs executed through your semantics terminate with
an empty k cell.

Finally, you may wish to visualize the search graph created by your search
command. For this purpose we provide the \verb^--graph^ flag to \krun. The
\verb^--graph^ flag tells \krun to output the search graph as a set of nodes
connected by edges corresponding to transition rules in your semantics. By
specifying this flag, you will receive a textual representation of this graph
for your examination. You will also be given the option to load this graph into
the \krun debugger in order to view it in more detail by examining specific
vertices and edges within the graph.  Future versions of the tool also plan to
allow you to export your graph to an xml format to be loaded by third-party
tools, or saved to a file and reloaded by the debugger at a later time.
*/

/*@
\subsubsection{Debugging programs: \texttt{-{}-debug}}
\label{sec:debugger}

Frequently, one of the applications of a programming language that you desire
is the ability to observe how a program executes as it is executing. For this
purpose, \krun provides a built-in set of debugging facilities.  By executing a
program in \krun with the \verb^--debug^ flag, you tell \krun to create an
instance of the debugger to use to manually explore the state space of the
program.

When you first execute a program in the debugger, it begins by automatically
executing until the first transition point in the semantics. For this reason,
it is necessary to first tune your semantics for nondeterminism before using
the debugger. For information on this process, please refer to
section \ref{sec:nondeterminism}.

Once you have reached the first transition point in the semantics, the debugger
halts for user input. At this point, you can specify a number of different
commands to the debugger. To refer back to this list of commands while
debugging, type the \verb^help^ command. Similarly, to exit the debugger at any
time, type the \verb^abort^ command.

The remaining commands serve the purpose of allowing you to manually explore
the state space of your program, and to construct a search graph of these
states. Essentially, you may select any state in your program and tell \krun to
execute from that state for some specific amount of time. When the debugger
returns control to you, it will have added the states it passed through while
performing your command to the search graph, and you will be able to view them.

For this purpose, \krun provides four basic commands to control your
interaction with the search graph. First of these is the
\verb^show-search-graph^ command. This command prints a summary of the entire
search graph as it has been constructed so far. Each state in the graph is
given a unique number, and each edge provides whatever basic information the
debugger has been able to learn about that edge (i.e. its label or its tags).

Before you can execute from a particular state, you must first select it with
the \verb^select^ command. By passing this command a state number, you tell the
debugger that future commands to further explore the state space of the program
should begin in that state. This is not necessary if your desire is to begin
executing in the state you had just created. However, if you have immediately
previously executed a command which generated more than one leaf state, or if
you wish to execute from a different state than the leaf state you have just
created, you need to first use this command to select the state in question.

Finally, \krun allows you to request additional information concerning states
or edges in the graph. By using the \verb^show-node^ command, you may tell the
debugger to display the entire configuration for a particular state number. You
may also use the \verb^show-edge^ command to tell the debugger to display all
the information it has on a particular edge. Sometimes this is only the
contents of the configurations at the two endpoints of the edge. Other times
this also includes additional information like the label of the rule, or the
entire rule itself.

The remaining commands in the debugger serve the purpose of allowing you to
manually create new nodes in the search graph by executing some number of
steps. The simplest of these commands is the \verb^resume^ command. By
specifying this command, \krun proceeds to execute from the current state until
the program terminates. This will not provide you with any information
concerning the edges you pass through along the way, but it will construct
every single unique state between the state you began in and the termination of
the program. It also automatically selects the final state it returns.

If instead you wish to only proceed for some finite number of steps, you may
use the \verb^step^ command. This command behaves identically to the
\verb^resume^ command except that in addition to terminating if the program
reaches a final state, it also terminates after executing a fixed number of
steps. By default this is only a single step, but you may pass as an argument a
different number of steps for a bound as well. This command also automatically
selects the last state stepped through.

Finally, sometimes you may wish to examine the nondeterminism of a program, or
to gain further information about the edges of a particular segment of
execution. For this purpose we provide the \verb^step-all^ command. By default,
this command constructs all possible states exactly one step away from the
state you had previously selected to begin in. However, you may also increase
the depth of this command by passing it an argument of a number of steps.

The \verb^step-all^ command also serves to fill in any additional information
about the edges in the search graph it creates. Due to a current limitation of
the tool, edges created by means of superheating will only provide you with the
knowledge that they are superheated edges. However, a future version of the
tool will also provide you with the syntax production in your semantics which
was superheated. You may also even currently obtain the entire rule
corresponding to a \verb^--transition^ rule.

It is also planned in future versions of the tool to provide a graphical API to
the debugger to allow you to visualize the search graph in two dimensions, and
to allow you to save the search graph to an xml format to be loaded by the
debugger later, or to be used by third-party tools. Finally, it is also planned
to allow execution via the \verb^step^ and \verb^resume^ commands to be
terminated partway through by sending the SIGINT signal to the debugger.
*/


/*@
\subsubsection{Debugging programs graphically: \texttt{-{}-debug-gui}}
\label{sec:debugger-gui}

The graphical debugger comes as an extension of the textual one, allowing the
user to visualize the search graph information in a two dimensional manner. In
order to access the graphical debugger you have to execute a program in \krun
with the \verb^--debug-gui^ flag.

Example: krun program.ext \verb^--debug-gui^

This type of execution instantiates a new window containing:

\tab{    1. a panel for graph visualization (see section \ref{sec:Graph_panel})}

\tab{    2. a panel for displaying the configuration (see section \ref{sec:Configuration_panel})}

\tab{    3. a command area with buttons (see section \ref{sec:Command_area})}

\tab{    4. a menu for save, load or export operations. (see section \ref{sec:Menu})}

\paragraph{Graph_panel}
\label{Graph_panel}
The "Graph panel" represents the location which will hold the current search graph
of the program. Results of future exploration operations will be visible in this
area. As in general, the graph is comprised of vertices (see Section \ref{sec:Vertex})  and edges (see Section \ref{sec:Edge}).

\label{Vertex}
A vertex represents a certain state of the program. A vertex has a "Config id"
label, where the id is specific for each state individually.
Vertices can be selected. Selection is performed by left clicking the
vertex. The label of the vertex is highlighted with a red color so that the user can be
constantly aware of the current selection.

Also available is the selection of multiple vertices. This can be accomplished in two
ways:

\tab{    1. by holding the "Shift" key while left clicking on the vertices of choice }

\tab{    2. by holding the left click and moving the cursor to cover the entire area where the
vertices to be selected are placed.}

The results of selection are further discussed in
the "Configuration panel" paragraph (see Section \ref{sec:Configuration_panel}), as well as in the
"Command area" section (see Section \ref{sec:Command_area}).

One final action that can be performed is centering the selected vertex inside the graph layout.
To accomplish this, you have to hold the "Ctrl" key while selecting a vertex.
This will generate a transition which will position the vertex in the middle of the graph panel area.

\label{Edge}
Edges connect the vertices, retaining information about the transition applied and offering a
hierarchical manner of data interpretation. Single selection is possible even upon edges. Left
clicking an edge will open a new frame, further details about this frame being found in the
"Difference between states panel" section (see Section \ref{sec:Difference_between_states_panel}).

The execution of the graphical debugger is identical with that of the textual debugger,
in what regards the processes that are conducted in the background. An automatic execution until the
first transition point in the semantics is launched. Once this state is reached, the debugger halts for
user input. In consequence, the graph panel initially contains two vertices. The uppermost one is equivalent
to the original state of the program, whilst the other one is obtained after the previously mentioned
automatic execution. Additions to the graph will be dictated by the users exploration actions.

Taking into account the size of the graph that can become considerably large, ZOOM-IN and ZOOM-OUT
capabilities are enabled. To zoom in or out, the user must position his cursor inside the reserved
area of the graph panel and utilize the scroll of the mouse to zoom in or out.
This way the graph can be manipulated and better controlled.

To a degree, the graph panel can be interpreted as the visual correspondent of the \verb^show-search-graph^
command from the textual debugger. The common element is represented by the fact that the purpose of both
concepts at hand is to display the entire search graph that has been constructed so far. The difference
surfaces from the manner of presentation, as well as from the scope of visibility of the graph. In the case
of the graphical debugger, the graph is always visible and is automatically modified according to the users actions.


\paragraph{Configuration_panel}
\label{Configuration_panel}

The "Configuration panel" provides more specific information about a certain state. As mentioned in
the "Graph panel" section (see Section \ref{sec:Graph_panel}), the graph contains all the currently
constructed states, represented as vertices with labels. Apart from these labels, states have associated
different configurations, which are key points of interest in investigating the behaviour of a program.
To display a configuration at choice just select the corresponding vertex from the graph panel.

After selection, the configuration panel will be updated with the proper configuration of that state
outputted in an XML format. The option of having multiple configurations opened for view without updating
the current panel is available. When a user selects multiple vertices(see section \ref{sec:Vertex}), each vertex
configuration will be display in a tabbed panel in the area reserved for visualizing cell states.
To avoid confusion, only one configuration is shown at a time, but the process of interchanging the viewed
configuration is as simple as clicking the tabbed panel associated with the wanted vertex. To close a tabbed
panel simply deselect the correspondent vertex.

On account of the XML format , the printed cells of the configuration can be further processed.
A cell can be collapsed by pressing the "-" symbol which accompanies the start tag of the cell.
By doing so, the entire content of that cell will be replaced with a closed tag. To expand a
collapsed cell click the "+" symbol which appears in front of it.
The configuration panel acts like a global handler for all the existing states.
What that means is that all the expand and collapse
actions performed in a configuration are memorized and applied to a distinct configuration when
a different state is chosen from the graph. For example, if a user collapses the k cell of a
configuration, this cell will appear collapsed no matter the vertex selected from the graph panel.

Initially all cells are expanded. By adding the ability of manipulating the content of the configuration,
the user is able to obtain a better view of the information that is essential for his process of
evaluating the programs behaviour.

\paragraph{Command_area}
\label{sec:Command_area}
The "Command area" reveals the actions available for user execution in form of accessible buttons.
These are in order:

\tab{ #Step (see section \ref{sec:Step})}

\tab{ #Step-all (see section \ref{sec:Step_all})}

\tab{ #Collapse (see section \ref{sec:Collapse})}

\tab{ #Expand (see section \ref{sec:Expand})}

\tab{ #Compare (see section \ref{sec:Compare})}

\tab{ #Help }

\tab{ #Exit (see section \ref{sec:Exit})}

The first two buttons of the list are equivalent to the commands with the same name from
the textual debugger.

The other four buttons are specific to the graphical debugger and its manner
of data representation.

In addition, this area contains an input box where the user can enter the
number of steps that need to be passed to the debuggers background processes and executed.

\label{Step}
The "Step" button performs an action which behaves identically to the \verb^step^ command from the
textual debugger.

\tab{  1. Select from the graph panel (see section \ref{sec:Vertex})
the vertex which holds the state from which to begin the execution. }

\tab{ 2. Write the number of steps to be executed in the input box of the command area. (default one step)}

\tab{ 3. Press the "Step button". }

 The command is executed and the resulting states of this action are
automatically added to the already constructed search graph. Once the graph is updated with the new
components, it is immediately redrawn to display the current information inside the graph panel.

As a final phase of the "Step" command, the last state added in the graph is by default selected for the user.

Another feature of the "Step" command is that it can be applied to a group of vertices from the graph,
not just one. The stages to be followed for this type of action are identical to those previously
described for the "Step" command, with the exception that a multiple selection should be done upon
the graph panel(see section \ref{sec:Graph_panel} multiple selection). The number of given steps will be executed
for each and every vertex of the selection and all of the resulting states and corresponding edges will
be inserted in the graph panel. All final states for every initially chosen vertex will be selected automatically.

The graph has unique components. No vertex containing a state can appear more than once inside the graph.

\label{Step_all}
The "Step-all" button is the correspondent of the \verb^step-all^ command from the textual debugger.

\tab{ 1. Select wanted vertex or group of vertices.}

\tab{ 2. Give number of steps to be executed (default 1) in the input box.}

\tab{ 3. Press "Step-all" button.}

\tab{ Result: All successors in the entered number of transitions are computed and the newly created vertices and
edges are properly placed inside the graph panel.}

\label{Collapse}
The "Collapse" button offers data manipulation support. Because the search graph can become difficult
to handle due to dimension concerns, the user is given the ability to reduce the number of visible
graph components.

\tab{ 1. Select vertices that should be collapsed. }

\tab{ 2. Press "Collapse" button.}

\tab{Result:  The selected group of vertices are mashed up into one graph component.}

The changes are observable in the graph panel.
The new component which accommodates a number of basic vertices has distinct properties.
The shape of this component is dictated by the number of vertices it holds. This translates to a new
triangle shaped component being added if 3 vertices were collapsed, or a square shaped in the case of
4 vertices and so on. The label for this component lists the configuration ids for the vertices which
were compressed.

The button can be used only in certain conditions and if those requirements are not fulfilled it becomes
disabled. The condition for enabling this button is to select at least 2 vertices from the graph.
Another important aspect is that collapsing extends not only to basic vertices. Any combination of more
than two graph elements (normal vertices, collapsed components) can be the subject of collapsing.

\label{Expand}
The "Expand" button represents the complementary action of the "Collapse" button. Information prioritizing
can be modified and a collapsed vertex should have the option of being brought back to a detailed view.

\tab{1. Select the compressed component that should be expanded.}

\tab{2. Press "Expand" button.}

\tab{ Result:  The graph is redrawn and the elements
which formed the collapsed component are once again available in the displayed search graph.}

The enabling of this button is conditioned by selecting a composed graph element.

\label{Compare}
The "Compare" button has the purpose of easing the workload to which the user has to be submitted to in order to
perceive the differences between configurations.

\tab{ 1. Select 2 basic vertices.}

\tab{ 2. Press the "Compare" button.}

\tab {Result: A new window appears displaying the "Difference between states panel" (see section \ref{sec:Difference_between_states_panel}).}

\label{Exit}
The "Exit" button represent the manner in which the user can stop the execution
of the graphical debugger. Clicking this button will close the window associated to
the debugging session.

\paragraph{Difference_between_states_panel}
The "Difference between states panel" contains two configurations, displayed next to each other, one on the
left half of the panel and the other on the right half.

The differences between the two configurations are
highlighted for the user with a yellow color. This way the user can easily remark what has changed and
what remains common for the two selected elements.

\paragraph{Menu}
\label{sec:Menu}

\ref{sec:Save}

\ref{sec:Load}

\ref{sec:Export}


\label{Save}
The "Save configuration" option enables the user to retain an exact state of a vertex(vertices) in a file(files).
It could be the case that a certain configuration can be of great interest or that the execution is halted and we want to restart
the process of debugging from where we left if off.

To save a configuration just select a vertex(or vertices) from the Graph Panel,
press File and then Save Configuration. Then choose the location where the file which stores the configuration should be saved.

Shortkey: Ctrl+S.


\label{Load}
Press File -> Load Configuration to load a specific file of your choice.

Shortkey: Ctrl+L.

\label{Export}
Graph representations can be exported in a .png format by clicking File -> Export png.

Shortkey: Ctrl+P.

*/

/*@
\subsubsection{LTL Model Checking: \texttt{-{}-ltlmc}}

\bluetext{(Dorel)}
*/

/*@

\subsubsection{External parsers: \texttt{-{}-parser}, \texttt{-{}-cfg-parser}}
\label{sec:external-parsers}

Up to this point we have been operating under the assumption that your desire
is only to use the default parsing options for parsing terms provided as inputs
to \krun. However, sometimes you will find that it is simply not possible to
parse a particular language using the \K framework. Because of this limitation,
it is intended that you be able to specify external parsers for your language
which can be used instead of the default parser in order to parse programs and
terms in such languages.  Because of this, \krun provides several options
designed to allow you to choose how you wish to parse terms that are inputs to
\krun, as well as also providing a number of intelligent defaults.

The simplest form of parsing occurs when you specify a file as an argument on
the command line. By default, this parses the contents of that file using the
\kast command with no options. For example, if I write the command
\verb^krun foo^, it will in term execute the command \verb^kast foo^ which will
assume that foo is a file on the file system containing a program written in the
syntax of the language. For details concerning how \kast operates, please refer
to section \ref{sec:kast}.

In order to specify an external parser for this purpose, the \verb^--parser^
flag is used. By specifying a shell command as argument to this flag, that
shell command gets executed with a single argument: the value of the argument
to \krun. Normally this is the path to a file containing code to be parsed.
However, this is not necessarily a guarantee. For example, the command
\verb^krun --parser "kast -e" "foo"^ will execute the command
\verb^kast -e foo^ which will in turn assume that ``foo'' is a valid program in
the language of the semantics you have defined (as opposed to the name of a file
containing such a program).

However, unfortunately, sometimes the name of the file (or the term itself) is
not sufficient information in order to be able to successfully parse a value.
In order to remedy this, and instead of requiring that external parsers be able
to parse flags on the command line, \krun also sets a number of environment
variables in the environment of the process created for the external parser.
These environment variables provide additional information in order to allow
the external parser to make additional decisions concerning how to parse
something, or not, as it chooses. Currently \krun sets three of these.

The first, KRUN\_COMPILED\_DEF, contains the absolute path to the compiled
definition directory on the file system, in case the external parser wishes to
use this. This is especially useful if your external parser is a variant of
\kast.

The second, KRUN\_SORT, contains a sort name designed to provide the external
parser information about the context in which the term is being parsed. As an
example of how this is used, if you specify a model-checking formula using the
\verb^--ltlmc^ flag, it is parsed using your external parser with the sort
information of ``LtlFormula''.

The third, KRUN\_IS\_NOT\_FILE, tells the external parser that because of the
particular type of value being parsed, by default it is being passed as an
argument on the command line instead of as a name to a file containing data to
be parsed. For example, configuration variables, when parsed by an external
parser, set this value. Note that this does not necessarily mean that the value
actually being passed doesn't consist of a filename. A parser may behave
however you wish it to, and as long as it receives an input it can understand,
this is acceptable behavior. The flag merely indicates that unless you specify
an external parser, the value provided is being assumed to be data to be parsed
rather than a filename. This allows the same parser to be used both with a
filename and with data to be parsed, without needing to specify separate parser
commands for each.

It is worth noting the \verb^--parser^ flag, while used for programs,
model-checking formulas, \verb^--term^ values, and runtime parsing of \#String
constants, is not used to specify parsers for configuration variables. This is
because a limitation of the Apache CLI framework used to parse command line
arguments makes it impossible to determine where within a command line string
an argument (i.e. not an option) is specified. However, since it is possible to
obtain this information for options, it is used in the design of how you
specify external parsers for configuration variables.

The \verb^--cfg-parser^ flag behaves similarly to the \verb^--parser^ flag in
that it takes a string to be used as the command for parsing configuration
variables. However, since it is possible to specify multiple configuration
variables, it is desirable to allow these configuration variables to be parsed
each with different parsers. Therefore, when determining which parser to use to
parse a particular configuration variable, the parser chosen is the one
specified by the rightmost \verb^--cfg-parser^ flag which is to the left of the
\verb^-c^ flag in question. Additionally, by default, since most configuration
parameters contain things like Lists and Maps and other pieces of syntax not
provided by the default \kast parser, the default parser for configuration
variables is \verb^kast -groundParser -e^. Please refer to section \ref{sec:kast} for
details on how this command behaves.

Because \krun parses a number of different types of inputs, each of which
consisting of a different sort of data, it is reasonable to expect that it will
use a number of different types of behavior when deciding which parser to use
to parse that data. For reference, therefore, the following table contains all
the information concerning how each type of data parsed by \krun is parsed by
default, and how it can be customized.

\begin{tabular}{|p{3.5cm}|l|l|l|p{3.6cm}|}
\hline
Type of data parsed & Default parser & Parser flag & KRUN\_SORT & KRUN\_IS\_NOT\_FILE \\ \hline
\verb^--pgm^ and command line arguments & \kast & \verb^--parser^ &  & \\ \hline
\verb^--term^ & \verb^kast -groundParser^ & \verb^--parser^ &  & \\ \hline
\verb^-c^ & \verb^kast -groundParser -e^ & \verb^--cfg-parser^ &  & \verb^true^ \\ \hline
\verb^--pattern^ & \verb^kast -ruleParser -e^ &  &  & \\ \hline
\verb^--ltlmc^ & \kast & \verb^--parser^ & \verb^LtlFormula^ & \verb^true^ if the argument provided is not a file, \verb^false^ otherwise \\ \hline
\verb^#parse(Term, Sort)^ & \kast & \verb^--parser^ & \verb^Sort^ & \verb^true^ \\ \hline
\end{tabular}

*/

/*@
\subsubsection{\krun execution backends: \texttt{-{}-backend}}
By default, once an initial configuration has been computed by \krun{}, the
actual executing of the rewriting-based semantics is performed by maude.
However, for certain purposes, maude is less than ideal. For example, maude's
implementation of Sets, Bags, and Maps is based on associative-commutative
matching, which, while incredibly powerful and capable of supporting very
complex operations on these data types, is highly inefficient. Additionally,
certain applications of the k-framework are highly string-intensive, such as
performing program verification which requires the construction of SMT-LIB 2
strings. Unfortunately maude's string implementation has no support for
buffered construction of strings, and so the construction of large strings in
maude is highly inefficient. These two examples are simply two of a number of
reasons why it is not always the case that Maude provides the optimal solution
for executing programs in \krun{}.

For this purpose, we provide the ability to utilize other execution backends,
as they become implemented by the framework. In order to specify these
backends, it is necessary to pass to \krun the \verb^--backend^ flag. This
flag takes a string representing the name of a \krun execution backend, and
then, once it is time to begin rewriting, passes off the task of executing
the program to this backend. Currently the only backend supported other than
the default of maude is the java-symbolic backend, whose purpose is to
symbolically execute terms containing variables according to the mathematical
domains of the semantics and the mathematical notion of satisfiability and
validity. We plan, however, to also support a very efficient backend in java
for normal usage, in order to overcome the performance inefficiencies
introduced by using maude.
*/

/*@
\subsubsection{Output formats: \texttt{-{}-output-mode}, \texttt{-{}-output},
\texttt{-{}-color}, \texttt{-{}-statistics}, \texttt{-{}-trace}, \texttt{-{}-profile}}

\krun supports a number of distinct modes for specifying output. The most
obvious of these pieces of functionality is the \verb^--output-mode^ flag. This
flag supports four different values. Simplest of these is ``none'', which tells
krun to display no output except that which was printed to the console or to
files by I/O in the program executing. The second, ``pretty'', is also the
default, and tells \krun to pretty-print the output it receives from its
backend. For normal execution, this means that it re-concretizes the syntax
that was flattened by \kompile, and displays it to the user. For search, this
means that we display the list of search results (or the list of substitutions)
which has also been re-concretized. For model-checking, this means either
displaying the fixed constant \verb^true^ to represent a model-checking which
has succeeded, or displaying a graph consisting of the re-concretized states
composing the LTL counterexample returned by a model-checking which has failed.

The third value is ``raw''. A raw output simply takes the output printed by the
maude backend and provides it unchanged to the user. Finally, the fourth value,
``binary'', saves the resulting configuration of an execution to a binary format
that can be used later to resume computation (see section \ref{sec:kast}).
Output mode ``binary'' is currently not supported by search or model-checking,
but future versions of the tool will save these results to a format which can
be loaded by the debugger (see section \ref{sec:debugger}).

By default (except in the case of output mode ``binary'', which always saves to a
file), the output is printed to stdout. However, sometimes it is desirable to
separate the output provided by krun from the output provided to stdout by I/O
in your program. In order to do this, we have provided the flag
\verb^--output^. This flag accepts as a single parameter the path to a file,
which it writes the output to.

Finally, there are several other miscellaneous options which have an effect on
how the output of \krun is printed. For example, the \verb^--color^ flag tells
\krun to pretty-print cells in the color specified in the configuration (see
section \ref{sec:configurations}). Since this is also the default, primarily you will
be using its inverse flag, \verb^--no-color^, which is useful if you wish to
pipe the output printed to stdout to a file. Since colors are printed using
8-color ANSI terminal color codes, if you specify the \verb^--output^ flag, the
default becomes \verb^--no-color^. If for some reason you wish to preserve
these color codes in the output file, you may still specify the \verb^--color^
flag manually.

Also present is the flag \verb^--statistics^, which parses statistics returned
by maude about the execution of a program and prints them to the user. Due to
limitations of the tool, currently this is only supported for program
execution, but it is planned to also support search and model-checking in a
future release.

Finally, there are two other pieces of functionality that krun exposes for
output via the ``raw'' output mode only. These correspond to access to maude's
internal tracer and profiler, respectively. By specifying \verb^--trace^, you
tell \krun to tell maude to output the entire trace of all rewriting done to
the file it internally writes its output to, which is displayed to the user via
output mode ``raw''. A note of warning here: because it is I/O intensive and
maude otherwise performs a very high number of rewrites per second, the trace
feature is incredibly slow, and should be used with caution.

Additionally, by specifying the flag \verb^--profile^, you tell \krun to tell
maude to construct profiling information on all the rules executed by the
semantics. This is useful if you wish to examine whether there are any rules
which are matching or applying too often. It's worth noting here however, that
since the primary speed bottleneck in maude is associative-commutative
matching, it is not always the case that decreasing the number of times a rule
rewrites will have an appreciable effect on performance, even if that rule
executes millions of times. In the absence of AC matching, maude rewrites
several million rules per second. AC matching, however, is over 100 times
slower.
*/

/*@
\subsection{Parsing \K Programs: \kast}
\label{sec:kast}
\bluetext{(Radu, Stefan)}

*/

/*@
\section{Libraries }
\bluetext{(Traian,Brandon, Grigore, Dorel}

*/


/*@
\subsection{Basic Data Types}

\subsubsection{Identifiers}

\subsubsection{Integers}

\subsubsection{Booleans}

\subsubsection{Floats}
*/

/*@
\subsubsection{Strings}

A String in \K corresponds to an indexable, searchable array of Unicode code
points, as represented by literals enclosed in double quotes. For example,
\verb^""^ is the empty string, and \verb^"string"^ is a string of length 6.
While most ASCII characters can be encoded simply by typing them, non-ASCII
characters in \K definitions, as well as some ASCII characters, require escape
sequences to encode themselves in strings. \K provides, in addition to the
standard escape sequences \verb^\t^, \verb^\n^, \verb^\r^, \verb^\\^, and
\verb^\"^, three mechanisms for escaping characters. The first, \verb^\x^,
takes exactly two hexadecimal digits as argument, and encodes the Latin-1
Unicode code point corresponding to that number. The second, \verb^\u^, takes
exactly four hexadecimal digits as argument, and encodes a Unicode character
in the Basic Multilingual Plane.

For portability reasons, a String in \K is a sequence of code points, not a
sequence of code units. Therefore, the escape sequences in the range
\verb^\ud800^ to \verb^\udfff^, corresponding to UTF-16 surrogate pairs, are
not allowed in String literals. If you believe that this impairs your ability
to write the semantics you desire in the \K framework, please let us know. We
are willing to re-evaluate this decision. However, you might simply consider
disallowing such strings in your semantics, as they do not correspond to any
well-encoded Unicode String, and the Unicode standard forbids their use outside
of UTF-16 surrogate pairs. Alternatively, you may choose to represent strings
as an array of bytes or an array of integers in your semantics, and implement
encoding and decoding yourself.

The third and final escape sequence \K provides is \verb^\U^, which takes
eight hexadecimal digits encoding any Unicode code point, from
\verb^\U00000000^ all the way up to \verb^\U0010ffff^.

The \K framework defines the following operations on Strings:

\begin{verbatim}
syntax String ::= String "+String" String

syntax Bool ::= String "==String" String
              | String "=/=String" String
              | String "<String" String
              | String ">String" String
              | String "<=String" String
              | String ">=String" String

syntax Int ::= lengthString(String)

syntax String ::= chrChar(Int)
syntax Int    ::= ordChar(String)

syntax String ::= substrString(String, Int, Int)
syntax Int ::= findString(String, String, Int)
             | rfindString(String, String, Int)

syntax Int    ::= String2Int(String)
syntax String ::= Int2String(Int)

syntax String ::= categoryChar(String)
                | directionalityChar(String)
\end{verbatim}

The \verb^+String^ operation performs String concatenation. The \verb^==String^
operation performs String equality, the \verb^=/=String^ inequality, and the
remaining four comparisons perform lexicographic ordering on Strings. The
\verb^lengthString^ operation returns the number of code points in the String.
\verb^ordChar^ and \verb^chrChar^ convert between single unicode characters
and their numeric code points. Again, as before, unicode code points in the
surrogate range cannot be encoded in Strings in \K.

\verb^substrString^ takes a string, an inclusive begin offset, and an exclusive
end offset, and returns the characters between that range. \verb^findString^
takes two strings and an inclusive offset, and returns the index of the first
occurrence of the second string in the first string which follows the provided
offset. \verb^rfindString^ performs the same task but searches from right to
left.

\verb^String2Int^ converts a String into an integer by means of parsing it. A
String that can be converted to an integer is either a sequence of characters
with the "Nd" general category, optionally preceded by a sign, or else a
single character with a Numeric Value unicode property which corresponds to
an integer.  \verb^Int2String^ converts back from an integer to a string by
means of the ASCII digit characters.

Finally, several methods exist to support reflection into the Unicode character
database. \verb^categoryChar^ returns the two-letter string code corresponding
to the general category of the character provided as argument, and
\verb^directionalityChar^ provides the string code of the bidirectionality
category of the character.
*/

/*@
\subsection{Polymorphic Data Types}

\subsubsection{Lists}

\subsubsection{Sets}

\subsubsection{Maps}

\subsubsection{Bags}

*/

/*@
\subsection{Operations on ASTs}

\subsubsection{Generic Pattern Matching}

\subsubsection{Substitution}

\subsubsection{Unification}

*/

/*@

%\bibliographystyle{plain}
%\bibliography{k}

\alert{References???}

*/

/*@
%\makeindex

\alert{Index???}
*/
