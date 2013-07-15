/*!
\setlength{\parindent}{1em}
\title{CinK -- an experiment on how to think in \K}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro}) and 
        Traian Florin \c{S}erb\u{a}nu\c{t}\u{a} (\texttt{traian.serbanuta@info.uaic.ro})}
\organization{Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\myparagraph}[1]{\textbf{#1}}
\newcommand{\KTool}{\K tool\xspace}
\newcommand{\Cink}{CinK\xspace}
\newcommand{\Cpp}{\mbox{C\raisebox{.2ex}{\small\!+\!+}}\xspace}
*/

/*@ \section{Introduction}

\Cink is a kernel of the \Cpp language we used to experiment with \K.
The language is used
an example for teaching classes and is refered in several research papers.

We assume the reader is already familiar with the \K Framework and the 
\KTool and here we try to share our experiece in defining a languages with some
specific features, as \Cpp is. 

\Cink is developed in several iterations, each iteration adding an incremental 
contribution.

This file extends the basic iteration 
with the mechanisms able to handle pointers.

Here is the definition of the indirect operator from the \Cpp 2011 manual:
\begin{quote}
The unary * operator performs indirection: the expression to which it is 
applied shall be a pointer to an
object type, or a pointer to a function type and the result is an lvalue 
referring to the object or function
to which the expression points. If the type of the expression is 
\emph{pointer to $T$}, the type of the result is $T$.
\end{quote}
Related to the pointers is the ampersand (\&) operator:
\begin{quote}
The result of the unary \& operator is a pointer to its operand. 
The operand shall be an lvalue or a qualifiedid.
If the operand is a qualified-id naming a non-static member m of some 
class C with type T, the result has
type "pointer to member of class C of type T" and is a prvalue designating 
C::m. Otherwise, if the type of
the expression is T, the result has type "pointer to T" and is a prvalue that 
is the address of the designated
object (1.7) or a pointer to the designated function.
\end{quote}
*/

