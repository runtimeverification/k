require "intro.k"
require "imports-intro.k"
require "../../basic/cink-basic-syntax.k"
require "cink-arrays-unidimensional.k"

/*@ \section{Main Modules}

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




