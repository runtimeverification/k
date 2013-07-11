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

This file extends the initial iteration with the mechanisms able to handle
\emph{lvalues} and \emph{rvalues}.

Here are the definitions of these notions from the \Cpp 2011 manual:\\
\begin{quote}
-- An lvalue (so called, historically, because lvalues could appear on the 
left-hand side of an assignment expression) designates a function or an object.
[ Example: If E is an expression of pointer type, then
*E is an lvalue expression referring to the object or function to which E 
points. As another example, the result of calling a function whose return type
is an lvalue reference is an lvalue. --end example ]\\
-- An xvalue (an "eXpiring" value) also refers to an object, usually near
the end of its lifetime (so that its resources may be moved, for example). 
An xvalue is the result of certain kinds of expressions involving
rvalue references (8.3.2). [ Example: The result of calling a function whose 
return type is an rvalue reference is an xvalue. --end example ]\\
-- A glvalue ("generalized" lvalue) is an lvalue or an xvalue.\\
-- An rvalue (so called, historically, because rvalues could appear on the 
right-hand side of an assignment expression) is an xvalue, a temporary object 
(12.2) or subobject thereof, or a value that is not associated with an object.\\
-- A prvalue ("pure" rvalue) is an rvalue that is not an xvalue. 
[ Example: The result of calling a function whose return type is not a 
reference is a prvalue. The value of a literal such as 12, 7.3e5, or true is
also a prvalue. --end example ]
\end{quote}
*/
