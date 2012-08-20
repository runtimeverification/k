// Implementation of Unlambda (version 2) in K
// Language specification: http://www.madore.org/~david/programs/unlambda/


// This is a specification for a modified Unlambda syntax, produced by the
// accompanying lexer (lexer.sed).



module UNLAMBDA-SYNTAX

   syntax Fun ::= Atom         // atomic function
              |   Apply Fun Fun  // apply function to function

   syntax Apply ::= ">"       // apply token (`)

   syntax Atom ::= Normal
               |   Delay

   syntax Normal ::= First
                 |   Nonfirst

   syntax Nonfirst ::= Second
                   |   Third

   syntax Third ::= "s"        // "substitution"
 
   syntax Second ::= "k"       // "constant generator"

   syntax First ::= "i"        // "identity" 
               |   "v"         // "void"
               |   "." Int [strict]     // "print"
               |   "r"         // "carriage return"
               |   "e"         // "exit"
               |   "@"         // "read"
               |   "?" Int [strict]    // "compare character read"
               |   "|"         // "reprint character read"
               |   CallCC
               |   Continuation
               |   Promise

   syntax CallCC ::=  "c"         // "call with current continuation"

   syntax Delay ::=  "d"         // "delay"


   // Continuation and Promise are not in strict Unlambda syntax, and the
   // lexer should mark these as undefined

   syntax Continuation ::= "$"
   syntax Promise ::= "p"
      
endmodule

module UNLAMBDA
  imports UNLAMBDA-SYNTAX
  configuration
    <k> $PGM:Fun </k>
    <streams>
      <in stream="stdin"> $IN:List </in>
      <out stream="stdout"> .List </out>
    </streams>
    <settings>
      <tree> .Map </tree>  // representation of the program tree at any step
      <parent> .Map </parent> // parent pointers
      <child> .Map </child> // child pointers (pos = right; neg = left)
      <status> .Map </status> // traversal status
//      <eval> .Map </eval> // evaluations at nonterminals


       
      <leftdepth> 0 </leftdepth>
                    // depth of current node following left branches only
                    // i.e., number of right c-commanding nodes
      <rightccommand> .List </rightccommand>
                   // c-commanding nodes to the right of a node
                   // (terminology borrowed from generative syntax)
      <chain> .List </chain>
      <mode> 0 </mode>  // 0 = init, 1 = queue, 2 = eval
      <loc> 0 </loc>   // location of current eval

      <new> 0 </new>
      <next> 0 </next>
      <check> 0 </check>

      <queue> .List </queue>
      <prog> K:K </prog>
      <counter> 0 </counter>
    </settings>


  // Construct program tree with pointers

        // "parent" of root is 0 and thus has only one child
        // root is 1


  rule [InitializeTree]:
    <k> X:Fun </k>
    <mode> 0 => 1 </mode>
    <counter> 0 => 1 </counter>
    <queue> . => ListItem(0) ListItem(0) ListItem(X) </queue>
    
  rule [AddTerminal]:
    <mode> 1 </mode>
    <queue> ListItem(P:Int) ListItem(R:Int) ListItem(X:Atom) => . ...</queue>
    <counter> C:Int => C +Int 1 </counter>
    <tree>... . => C |-> X </tree>
    <parent>... . => C |-> P </parent>
    <child>... . => (P *Int R) |-> C </child>
    <status>... . => C |-> 0 </status>

  rule [AddNonterminal]:
    <mode> 1 </mode>
    <queue> ListItem(P:Int) ListItem(R:Int) ListItem(Z:Apply X:Fun Y:Fun) =>
              ListItem(C) ListItem(-1) ListItem(X)
              ListItem(C) ListItem(1) ListItem(Y) ...</queue>
    <counter> C:Int => C +Int 1 </counter>
    <tree>... . => C |-> Z </tree>
    <parent>... . => C |-> P </parent>
    <child>... . => (P *Int R) |-> C </child>
    <status>... . => C |-> 0 </status>

  rule [FinishTree]:
    <mode> 1 => 2 </mode>
    <queue> . </queue>

  
  // evaluation

  rule [StartTraversal]:
    <mode> 2 => 3 </mode>
    <loc> _ => 1 </loc>
//    <leftdepth> _ => 0 </leftdepth>
//    <chain> _ => . </chain>
    <status>... 1 |-> (_ => 0) ...</status>


  rule [TraverseTerminal]: 
    <mode> 3 => 4 </mode>
    <loc> L:Int => P </loc>
    <tree>... L |-> X:Atom ...</tree>
    <parent>... L |-> P:Int ...</parent>
   // <child>... P |-> L ...</child>
    <status>... L |-> (_ => 3) ...</status>

  rule [TraverseLeftChild]:
    <mode> 3 </mode>
    <loc> L:Int => C </loc>
    <tree>... L |-> Z:Apply ...</tree>
    <child>... N:Int |-> C:Int ...</child>
//    <parent>... M:Int |-> L ...</parent>
 //   <leftdepth> D:Int => D +Int 1 </leftdepth>
//    <chain> . => ListItem(L) ...</chain>
   when (N ==Int -1 *Int L) //andBool (M =/=Int C)

  rule [TraverseRightChild]: // only if not delay
    <mode> 4 => 3 </mode>
    <loc> L:Int => C </loc>
    <tree>... L |-> Z:Apply ...</tree>
    <child>... L |-> C:Int ...</child>
    <status>... L |-> (0 => 1) ...</status>
 //   <leftdepth> _ => 0 </leftdepth>
//    <chain> _ => . </chain>

    
  rule [ProcessNonterminal]:
    <mode> 4 => 11 </mode>
    <loc> L:Int </loc>
    <check> _ => C </check>
    <child>... N |-> C:Int ...</child>
    <tree>... L |-> Z:Apply ...</tree>
    <status>... L |-> (1 => 2) ...</status>
   when (N ==Int -1 *Int L)

  rule [TraverseNonterminal]: // resume traversal, no evaluation
    <mode> 5 => 4 </mode>
    <loc> L:Int => P </loc>
    <parent>... L |-> P:Int ...</parent>
    <status>... L |-> (2 => 3) ...</status>


  // degree checks
  rule [CheckFirstDegreeContinue]:
    <mode> 11 => 12 </mode>
    //<loc> L:Int </loc>
    <check> C:Int => G </check>
    <child>... N |-> G:Int ...</child>
    <tree>... C |-> Z:Apply ...</tree>
   when (N ==Int -1 *Int C)

  rule [CheckFirstDegreeMatch]:
    <mode> 11 => 21 </mode>
    //<loc> L:Int </loc>
    <check> C:Int </check>
    <tree>... C |-> Z:First ...</tree>

  rule [CheckFirstDegreeMatchDelay]:
    <mode> 11 => 21 </mode>
    //<loc> L:Int </loc>
    <check> C:Int </check>
    <tree>... C |-> Z:Delay ...</tree>

  rule [CheckFirstDegreeFail]:
    <mode> 11 => 5 </mode>
    <check> C:Int </check>
    <tree>... C |-> Z:Nonfirst ...</tree>

  rule [CheckSecondDegreeContinue]:
    <mode> 12 => 13 </mode>
    <check> C:Int => G </check>
    <child>... N |-> G:Int ...</child>
    <tree>... C |-> Z:Apply ...</tree>
   when (N ==Int -1 *Int C)

  rule [CheckSecondDegreeMatch]:
    <mode> 12 => 22 </mode>
    //<loc> L:Int </loc>
    <check> C:Int </check>
    <tree>... C |-> Z:Second ...</tree>

     // fail must be a third-degree; should not encounter first-degrees 
  rule [CheckSecondDegreeFail]:
    <mode> 12 => 5 </mode>
    <check> C:Int </check>
    <tree>... C |-> Z:Third ...</tree>

      // should not fail
  rule [CheckThirdDegreeMatch]:
    <mode> 13 => 23 </mode>
    <check> C:Int </check>
    <tree>... C |-> Z:Third ...</tree>


  // evaluations
  rule [EvaluateIdentity]: // i
    <mode> 21 => 31 </mode>
    <loc> L:Int </loc>
    <child>... N |-> C:Int ...</child>
    <tree>... C |-> i ...</tree>
   when (N ==Int -1 *Int L)

  


  rule [IdentityTransform1]: // erase left child
    <mode> 31 => 32 </mode>
    <loc> L:Int </loc>
    <new> _ => C </new>
    <child>... N |-> C:Int => . ...</child>
    <parent>... C |-> L => . ...</parent>
    <tree>... C |-> _ => . ...</tree>
    <status>... C |-> _ => . ...</status>
   when (N ==Int -1 *Int L)

  rule [IdentityTransform2]: // erase L
    <mode> 32 => 33 </mode>
    <loc> L:Int </loc>
    <child>... L |-> R:Int => . ...</child>
    <parent>... L |-> P:Int => . ...</parent>
    <tree>... L |-> _ => . ...</tree>
    <status>... L |-> _ => . ...</status>  

  rule [IdentityTransform3Left]: // remap
    <mode> 33 => 4 </mode>
    <loc> L:Int => 0 -Int Q </loc>
    <child>... Q:Int |-> (L => C) ...</child>
    <parent>... C:Int |-> (L => 0 -Int Q) ...</parent>
   when Q <Int 0
  
  rule [IdentityTransform3Right]: // remap
    <mode> 33 => 4 </mode>
    <loc> L:Int => P </loc>
    <child>... P:Int |-> (L => C) ...</child>
    <parent>... C:Int |-> (L => P) ...</parent>
   when P >=Int 0



//    <parent>... L |-> P:Int ...</parent>
//    <status>... L |-> (1 => 2) ...</status>

    
//    <eval> E:Map </eval>
//   when notBool(L in keys(E))


  




/*  // processability check should be at evaluation stage, not descent

  rule [ProcessFirstDegree]: //  i, v, .x, r, e, @, ?x, |
    <mode> 3 => 4 </mode>
    <loc> L:Int => P </loc>
    <tree>... L |-> X:First ...</tree>
    <parent>... L |-> P:Int ...</parent>
    <status>... L |-> (_ => 2) ...</status>
    <leftdepth> D:Int </leftdepth>
    <eval>... . => L |-> X </eval>
//    <chain> ListItem() ...</chain>
   when D >=Int 1
*/

/*
  rule [EvaluateIdentity]:  // i
    <mode> 74 => 5 </mode>
    <loc> L:Int =>  </loc>
    <tree>... L |-> Z:Apply ...</tree>
    <parent>... L |-> P:Int ...</parent>
    <status>... L |-> (1 => 2) ...</status>
    <eval>... L |-> "i" => . ...</eval>

  rule [Repeat]: // repeat traversal & evaluation on current subtree
    <mode> 5 => 3 </mode>
    <loc> _ => 1 </loc>
    <leftdepth> _ => 0 </leftdepth>
    <chain> _ => . </chain>
    <status>... 1 |-> (_ => 0) ...</status>

*/


  
// previous abandoned attempts at implementing program structure
  
/*
  rule [InitializeTree]:
    <k> X:Fun </k>
    <mode> 0 => 1 </mode>
    <loc> 0 </loc>
    <queue> . => 0 |-> X </queue>

  rule [QueueTerminal]:
    <mode> 1 </mode>
    <queue> P:Int |-> X:Atom => . ...</queue>
    <tree>... . => P |-> X </tree>
    
  rule [QueueNonterminal]:
    <mode> 1 </mode>
    <queue> P:Int |-> (Z:Apply X:Fun Y:Fun) =>
              (P *Int 2 +Int 1) |-> X (P *Int 2 +Int 2) |-> Y ...</queue>
    <tree>... . => P |-> Z </tree>
 
  rule [EndQueue]:
    <mode> 1 => 2 </mode>
    <queue> . </queue>
*/


/*

  rule [Initialize]:
    <k> X:Fun </k>
    <mode> 0 => 1 </mode>
    <counter> 0 </counter>
    <queue> . => ListItem(X) </queue>

  rule [QueueTerminal]:
    <mode> 1 </mode>
    <counter> C:Int => C +Int 1 </counter>
    <queue> ListItem(X:Atom) => . ...</queue>
    <prog>... . => X </prog>
    
  rule [QueueNonterminal]:
    <mode> 1 </mode>
    <counter> C:Int => C +Int 1 </counter>	
    <queue> ListItem(Z:Apply X:Fun Y:Fun) => ListItem(X) ListItem(Y) ...</queue>
    <prog>... . => Z </prog>
 
  rule [EndQueue]:
    <mode> 1 => 2 </mode>
    <queue> . </queue>


  rule [Identity]:
    <mode> 2 => 1 </mode>
    <prog>... Z:Apply "i" X:=> . ...</prog>

*/


/*  
  rule [Identity]:
    <mode> 2 => 1 </mode>
    <queue> . => L |-> Y </queue>
    <loc> L:Int </loc>
    <tree>... L |-> Z:Apply ...</tree>
    <tree>... M:Int |-> "i" => . ...</tree>
    <tree>... N:Int |-> Y:Fun => . ...</tree>
   when (M ==Int L *Int 2 +Int 1) andBool (N ==Int L *Int 2 +Int 2)
  */

  

endmodule
