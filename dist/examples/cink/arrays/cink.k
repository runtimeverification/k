require "../basic/cink-basic.k"
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

This file includes the starting iteration, where the basic constructions of 
\Cink as arithmetic and boolean expressions (partial), imperative 
statements, simple threads, are defined. The variables can be declared only in
the main block of the function. 


*/

/*@ \section{Syntax}
The syntax of \Cink is written using the last version at the moment of the 
\KTool. Since the language is relatively small, we use the facilities the 
\KTool offers for deffining the syntax.This is given using a BNF-like 
notation enriched with annotations and priority specifications.
In this way, the rules giving semantics are written using the \Cink 
syntax. 
*/

module CINK-SYNTAX 

  imports CINK-BASIC-SYNTAX
  imports CINK-ARRAYS-SYNTAX

endmodule

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




