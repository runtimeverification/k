// Google Code Jam: Old Magician
// http://code.google.com/codejam/contest/32004/dashboard#s=p0


// This is an exercise in problem solving in K by representing a problem
// as a language and implementing it. An input file is then treated as
// a program in the language, and its output corresponds to the solution to
// the problem for that given input.



module OLDMAGICIAN-SYNTAX
   syntax Program ::= Init Cases

   syntax Case ::= Int Int
 
   syntax Cases ::= Case
                  | Case Cases

   syntax Init ::= Int
endmodule


module OLDMAGICIAN
  imports OLDMAGICIAN-SYNTAX
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

  rule [FormatOutput]:
    <format> S:String => . </format>
    <case> C:Int </case>
    <out>... . => ListItem("Case #") ListItem(C) ListItem(": ")
                  ListItem(S) ListItem("\n") </out>


  // Individual Test Case

  rule [HandleCase-Black]:
    <compute> W:Int B:Int => . </compute>
    <format> . => "BLACK" </format>
   when B %Int 2 ==Int 1
 
  rule [HandleCase-White]:
    <compute> W:Int B:Int => . </compute>
    <format> . => "WHITE" </format>
   when B %Int 2 ==Int 0


endmodule
