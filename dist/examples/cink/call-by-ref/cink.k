require "intro.k"
require "imports-intro.k"
require "../pointers/cink-pointers.k"
require "cink-call-by-ref.k"


/*@ \section{The Main Module}
*/

module CINK
  imports CINK-POINTERS-SYNTAX
  imports CINK-CALL-BY-REF-SEMANTICS

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
