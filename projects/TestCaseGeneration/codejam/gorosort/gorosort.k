// Google Code Jam: GoroSort
// http://code.google.com/codejam/contest/975485/dashboard#s=p3


// This is an exercise in problem solving in K by representing a problem
// as a language and implementing it. An input file is then treated as
// a program in the language, and its output corresponds to the solution to
// the problem for that given input.



module GOROSORT-SYNTAX
   syntax Program ::= Tokens

   syntax Tokens ::= Int
                   | Int Tokens
endmodule


module GOROSORT
  imports GOROSORT-SYNTAX
  configuration
    <k> $PGM:Program </k>
    <streams>
      <out stream="stdout"> .List </out>
    </streams>
    <settings>
      <case> 1 </case>
      <total> 0 </total>
 
      <counter> 0 </counter>     
      <casesize> -1 </casesize>
      <compute> K:K </compute>
      <format> K:K </format>

      <index> 0 </index>
      <sum> 0 </sum>
    </settings>



  // Code Jam Infrastructure

  rule [Init]:
    <k> T:Int R:Tokens => R </k>
    <total> 0 => T </total>

  rule [InitCase]:
    <k> N:Int R:Tokens => R </k>
    <casesize> -1 => N </casesize>
    <counter> _ => 0 </counter>
    <compute> _ => . </compute>
     
  rule [ReadCase]:
    <k> X:Int R:Tokens => R </k>
    <counter> P:Int => P +Int 1 </counter>
    <casesize> L:Int </casesize>
    <compute>... . => X </compute>
   when P <Int L

  rule [Terminal]:
    <k> X:Int => . </k>
    <counter> P:Int => P +Int 1 </counter>
    <compute>... . => X </compute>
  

  rule [FormatOutput]:
    <format> I:Int => . </format>
    <case> C:Int => C +Int 1 </case>
    <out>... . => ListItem("Case #") ListItem(C) ListItem(": ")
                  ListItem(I) ListItem("\n") </out>


  // Individual Test Case

  rule [ProcessCase]:
    <counter> P:Int => 0 </counter>
    <casesize> L:Int => -2 </casesize>
    <index> _ => L </index>
    <sum> _ => 0 </sum>
   when P ==Int L


  rule [IndexMatch]:
    <casesize> -2 </casesize>
    <compute>... X:Int => . </compute>
    <index> I:Int => I -Int 1 </index>
   when X ==Int I

  rule [IndexMismatch]:
    <casesize> -2 </casesize>
    <compute>... X:Int => . </compute>
    <index> I:Int => I -Int 1 </index>
    <sum> S:Int => S +Int 1 </sum>
   when X =/=Int I

  rule [FinishCase]:
    <compute> . </compute>
    <sum> S:Int </sum>
    <format> . => S </format>
    <casesize> -2 => -1 </casesize>

endmodule
