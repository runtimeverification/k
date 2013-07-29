require "intro.k"
require "imports-intro.k"
require "syntax-intro.k"
require "cink-basic-syntax.k"
require "semantics-intro.k"
require "cink-basic-semantics.k"


/*@ \section{The Main Module}
Includes the modules defining the syntax and semantics, and defines 
the main configuration of the language.
*/



module CINK
  imports CINK-BASIC-SYNTAX
  imports CINK-BASIC-SEMANTICS

 /*@ \subsection{Configuration.} 
   The configuration is standard for such languages (compare it to that of IMPPP
   and SIMPLE).
  */


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
