require "intro.k"
require "imports-intro.k"
require "cink-pointers.k"


/*@ \section{Main Module}
 
*/

module CINK
  imports CINK-POINTERS-SYNTAX
  imports CINK-POINTERS-SEMANTICS

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
