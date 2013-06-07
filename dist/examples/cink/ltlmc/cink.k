require "../threads/cink-threads.k"
require "cink-ltlmc.k"

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

This file includes an extension of the \Cink-threads iteration with a small 
property language, including LTL formulas, and we show how the \KTool is used 
together with Maude system for analazing \Cink programs.

The definition must be parsed with the command

  kompile cink --transition="kripke"

in order to use the model-checker. The model against to the LTL formulas are
checked is the transitional system where the transitions are given by the
rules annotated with the tag "kripke".
*/

module CINK-SYNTAX 

  imports CINK-LTLMC-SYNTAX
  imports CINK-THREADS-SYNTAX

endmodule

/*@ \section{Semantics}
The semantics consists of the semantics of basic constructs together with the
that of arrays and the definition of the whole configuration: 
*/

module CINK
  imports CINK-SYNTAX
  imports CINK-BASIC-SEMANTICS
  imports CINK-THREADS-SEMANTICS
  imports CINK-LTLMC-SEMANTICS

  configuration <T color="yellow">
                  <threads color="pink">
                    <thread multiplicity="*" color="purple"> 
                      <name color="yellow"> noName </name>
                      <k color="green"> ($PGM:Pgm ~> execute) </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <fstack color="orange"> .List </fstack>
                    </thread>
                  </threads>
                  <genv color="SkyBlue"> .Map </genv>
                  <store color="white"> .Map </store>
                  <br/>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
                  <nextLoc> 0 </nextLoc>
                </T>

endmodule




