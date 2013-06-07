require "cink-arrays.k"

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

This file includes the extension of the starting iteration with 
multidimensional arrays. 

From C++ 2011 Manual:\\
  "In a declaration T D where D has the form\\
   \indent   D1 [ constant-expressionopt] attribute-specifier-seqopt\\
   and the type of the identifier in the declaration T D1 is 
   "derived-declarator-type-list T", then the type of the identifier of D
   is an array type...\\
   Example:
   \begin{verbatim}
      typedef int A[5], AA[2][3];
      typedef const A CA; // type is "array of 5 const int"
      typedef const AA CAA; // type is "array of 2 array of 3 const int"
  \end{verbatim}
  ... 
  "An array can be constructed from one of the fundamental types (except void),
   from a pointer, from a pointer to member, from a class, from an enumeration
   type, or from another array.\\
   When several "array of" specifications are adjacent, a multidimensional array
   is created; only the first of the constant expressions that specify the 
   bounds of the arrays may be omitted. In addition to declarations in
   which an incomplete object type is allowed, an array bound may be omitted in
   some cases in the declaration of a function parameter (8.3.5). An array 
   bound may also be omitted when the declarator is followed by an
   initializer (8.5). In this case the bound is calculated from the number of 
   initial elements (say, N) supplied (8.5.1), and the type of the identifier
   of D is "array of N T."
*/

/*@ \section{Syntax}
The syntax consists of the syntax of basic constructs together with the syntax
of arrays: 
*/

module CINK-SYNTAX 

  imports CINK-BASIC-SYNTAX
  imports CINK-ARRAYS-SYNTAX

endmodule

/*@ \section{Semantics}
The semantics consists of the semantics of basic constructs together with the
that of arrays and the definition of the whole configuration: 
*/

module CINK
  imports CINK-SYNTAX
  imports CINK-BASIC-SEMANTICS
  imports CINK-ARRAYS-SEMANTICS

  configuration <T color="yellow">
                  <control color="pink">
                      <k color="green"> ($PGM:Pgm ~> execute) </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <fstack color="orange"> .List </fstack>
                  </control>
                  <br/>
                  <genv color="SkyBlue"> .Map </genv>
                  <store color="white"> .Map </store>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
                </T>
endmodule




