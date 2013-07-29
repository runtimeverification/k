require "builtins/model-checker.k"
require "intro.k"
require "imports-intro.k"
require "../threads/cink-threads.k"

require "cink-ltlmc.k"

/*@  \section{The Main Module} */


/*@ \section{Semantics}
The semantics consists of the semantics of basic constructs together with the
that of arrays and the definition of the whole configuration: 
*/

module CINK

  imports CINK-LTLMC-SYNTAX
  imports CINK-THREADS-SYNTAX
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




