require "intro.k"
require "imports-intro.k"
require "../basic/cink-basic-syntax.k"
require "../basic/cink-basic-semantics.k"
require "cink-l-r-values.k"


/*@ \section{Main Module}
The semantics consists of the semantics of basic constructs together with
that of l-r-values and the definition of the whole configuration: 
*/

module CINK
  imports CINK-SYNTAX
  imports CINK-BASIC-SEMANTICS
  imports CINK-L-R-VALUES-SEMANTICS

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
