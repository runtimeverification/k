/*!
\setlength{\parindent}{1em}
\title{\K Reference Manual}
\author{\K Team}
\organization{University of Illinois at Urbana-Champaign, USA\\ Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\KTool}{\K tool\xspace}
\newcommand{\bluetext}[1]{\textcolor{blue}{\it #1\\}}
\newcommand{\alert}[1]{\textcolor{red}{\it #1\\}}


\titleformat{\section}{\bfseries}{\thesection.}{1em}{}
\titleformat{\subsection}{\bfseries}{\thesubsection.}{1em}{}
\titleformat{\subsubsection}{\bfseries}{\thesubsubsection.}{1em}{}
\titlespacing{\section}{0pt}{12pt}{6pt}
\titlespacing{\subsection}{0pt}{12pt}{6pt}
\titlespacing{\subsubsection}{0pt}{12pt}{6pt}
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

K has predefined the lexer rules for the most common syntactic categories that are directly accesible throught subsorting:
syntax #Bool   ::= Token{"true"} | Token{"false"}
syntax #Id     ::= Token{[a-zA-Z][a-zA-Z0-9]*}
syntax #Int    ::= Token{[\-\+]? [0-9]+}
syntax #String ::= Lexer{"\"" (~[\"\n\r] | "\\\"" | "\\")* "\""} // where '\' cannot be followed by double quote
syntax #Float  ::= Lexer{[0-9]+ "." [0-9]+ ([eE] #Int)}
syntax #Float  -/- [a-zA-Z0-9\.]

For some languages these may not be enough so you migth want to declare your own.
There are two main things that you have to consider: the regular expression that will do the matching, and the follow restriction. The later tells the regular expression when not to stop matching.

A regular expression for the matcher is similar to the one in SDF. Basically you may write strings, sets of tokens (using [...]), add optional arguments with '?'. You can negate a set of tokens by prefixing it with '~'. Inside a character set you may write individual caracters or entire ranges: a-z A-Z 0-9. Anything other than these need to be escaped using backslash.

The follow restriction is an important feature of the SDF parser, as the lexical rules are not greedy by default. The last line in the example above, says that #Float cannot be followed by one of the characters in the set. The list can be extended to check multiple characters ahead by concatenating sets with '.' (syntax X -/- [a].[b].[c]).

Sometimes you may also want to specify follow restrictions for keywords to avoid some ambiguities:
syntax "keyword" -/- [a-zA-Z0-9]

Another usefull construction is a list separated by a character. For example the name of a module in K is matched by a construction like the following:
syntax MODNAME ::= Lexer{"#"?{[a-z0-9A-Z\_]+ "-"}+}
syntax MODNAME -/- [a-z0-9A-Z\-\_]
The construction {<char set> "<separator>"}+ will match 'A', 'A-A', 'A-A-A', but not 'A-'.

Lexer{...} and -/- are the main way of specifying a lexical rule, but if your expression is simple enough, you may write Token{...}. This will try to infer automatically the follow restriction (if needed). Looking back at the rule for #Id, it will be equivalent to:
syntax #Id ::= Lexer{[a-zA-Z][a-zA-Z0-9]*}
syntax #Id -/- [a-zA-Z0-9]

Note that this works for simple expressions that have a repeated character set at the end. If you want to specify something more complex, you will have to use Lexer{...} and specify the follow restriction.



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
\subsection{Compiling \K Definitions}

\bluetext{(Traian, Radu, Andrei A)}
*/

/*@
\subsection{Running Programs with \K Definitions}

\bluetext{(Dwight)}
*/


/*@
\subsection{Analyzing programs}

\subsubsection{Stepper}

\bluetext{(Dwight)}

\subsubsection{Bounded Model Checking}

\bluetext{search options with varius suboptions (Dwight)}


\subsubsection{LTL Model Checking}

\bluetext{(Dorel)}


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

\subsubsection{Rational Numbers}

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
