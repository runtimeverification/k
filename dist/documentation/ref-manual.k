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

\subsubsection{Desambiguation Mechanisms}

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
