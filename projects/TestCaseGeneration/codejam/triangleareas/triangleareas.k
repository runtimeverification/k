// Google Code Jam: Triangle Areas
// http://code.google.com/codejam/contest/32001/dashboard#s=p1


// This is an exercise in problem solving in K by representing a problem
// as a language and implementing it. An input file is then treated as
// a program in the language, and its output corresponds to the solution to
// the problem for that given input.



module TRIANGLEAREAS-SYNTAX
   syntax Program ::= Init Cases

   syntax Case ::= Int Int Int
 
   syntax Cases ::= Case
                  | Case Cases

   syntax Init ::= Int
endmodule


module TRIANGLEAREAS
  imports TRIANGLEAREAS-SYNTAX
  configuration
    <k> $PGM:Program </k>
    <streams>
      <out stream="stdout"> .List </out>
    </streams>
    <settings>
      <case> 0 </case>
      <total> 0 </total>
      
      <compute> K:K </compute>
      <format> K:K </format>
    </settings>



  // Code Jam Infrastructure

  rule [Init]:
    <k> T:Init R:Cases => R </k>
    <total> 0 => T </total>

  rule [AdvanceCase]:
    <k> F:Case R:Cases => R </k>
    <compute> . => F </compute>
    <case> C:Int => C +Int 1 </case>
    <total> T:Int </total>
    <format> . </format>
   when C <Int T -Int 1

  rule [TerminalCase]:
    <k> F:Case => . </k>
    <compute> . => F </compute>
    <case> C:Int => C +Int 1 </case>
    <total> T:Int </total>
    <format> . </format>
   when C <Int T

  rule [FormatOutputString]:
    <format> S:String => . </format>
    <case> C:Int </case>
    <out>... . => ListItem("Case #") ListItem(C) ListItem(": ")
                  ListItem(S) ListItem("\n") </out>

  rule [FormatOutputNumbers]:
    <format> A:Int B:Int D:Int E:Int F:Int G:Int  => . </format>
    <case> C:Int </case>
    <out>... . => ListItem("Case #") ListItem(C) ListItem(": ")
                  ListItem(A:Int) ListItem(" ")
        	  ListItem(B:Int) ListItem(" ")
        	  ListItem(D:Int) ListItem(" ")
        	  ListItem(E:Int) ListItem(" ")
        	  ListItem(F:Int) ListItem(" ")
        	  ListItem(G:Int) ListItem("\n") </out>



  // Individual Test Case

  rule [Impossible]:
    <compute> N:Int M:Int A:Int => . </compute>
    <format> . => "IMPOSSIBLE" </format>
   when A >Int N *Int M

  rule [Possible]:
    <compute> N:Int M:Int A:Int => . </compute>
    <format> . => 0 1 N 0 ((A -Int 1) %Int N +Int 1)
                          ((A -Int 1) /Int N +Int 1) </format>
   when A <=Int N *Int M
 


endmodule
