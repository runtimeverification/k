// Google Code Jam: Store Credit
// http://code.google.com/codejam/contest/351101/dashboard#s=p0

// This is an exercise in problem solving in K by representing a problem
// as a language and implementing it. An input file is then treated as
// a program in the language, and its output corresponds to the solution to
// the problem for that given input.



module STORECREDIT-SYNTAX
   syntax Program ::= Tokens

   syntax Tokens ::= Int
                   | Int Tokens
endmodule


module STORECREDIT
  imports STORECREDIT-SYNTAX
  configuration
    <k> $PGM:Program </k>
    <streams>
      <out stream="stdout"> .List </out>
    </streams>
    <settings>
      <case> 1 </case>
      <total> 0 </total>
 
      <counter> 0 </counter> 
      <credit> 0 </credit>    
      <casesize> -1 </casesize>
      <map> .Map </map>

      <compute> K:K </compute>
      <format> K:K </format>

      <index> 0 </index>
    </settings>



  // Code Jam Infrastructure

  rule [Init]:
    <k> T:Int R:Tokens => R </k>
    <total> 0 => T </total>

  rule [InitCase]:
    <k> C:Int I:Int R:Tokens => R </k>
    <credit> _ => C </credit>
    <casesize> -1 => I </casesize>
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
    <format> A:Int B:Int => . </format>
    <case> C:Int => C +Int 1 </case>
    <out>... . => ListItem("Case #") ListItem(C) ListItem(": ")
                  ListItem(A) ListItem(" ") ListItem(B) ListItem("\n") </out>


  // Individual Test Case

  rule [ProcessCase]:
    <counter> P:Int => 0 </counter>
    <casesize> L:Int => -2 </casesize>
    <index> _ => L </index>
    <map> _ => . </map>
   when P ==Int L

  rule [IndexNotMatched]:
    <casesize> -2 </casesize>
    <credit> C:Int </credit>
    <compute>... X:Int => . </compute>
    <index> I:Int => I -Int 1 </index>
    <map> M:Map (. => X |-> I) </map>
   when notBool(C -Int X in keys(M))

  rule [IndexMatched]:
    <casesize> -2 => -1 </casesize>
    <credit> C:Int </credit>
    <compute>... X:Int => . </compute>
    <index> I:Int </index>
    <map>... Y:Int |-> J:Int ...</map>
    <format> . => I J </format>
   when C -Int X ==Int Y
 
endmodule
