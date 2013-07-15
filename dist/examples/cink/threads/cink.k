require "intro.k"
require "imports-intro.k"
require "../basic/cink-basic-syntax.k"
require "../basic/cink-basic-semantics.k"
require "cink-threads.k"


module CINK
  imports CINK-BASIC-SYNTAX
  imports CINK-THREADS-SYNTAX
  imports CINK-BASIC-SEMANTICS
  imports CINK-THREADS-SEMANTICS

 /*@ \subsection{Configuration.} 
   The threads are included in a cell named \texttt{threads}, where each cell
   \texttt{thread}, representing the current of a thread, includes a cell 
   \texttt{k} for the local computations, a cell \texttt{env} for the local
   environment.
  */

  configuration <T color="yellow">
                  <threads color="pink">
                    <thread multiplicity="*" color="purple"> 
                      <name color="yellow"> noName </name>
                      <k color="green"> ($PGM:Pgm ~> execute) </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <fstack color="orange"> .List </fstack>
                    </thread>
                  </threads>
                  <br/>
                  <genv color="SkyBlue"> .Map </genv>
                  <store color="white"> .Map </store>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
                </T>
endmodule




