// Implementation of Unlambda (version 2) in K
// Language specification: http://www.madore.org/~david/programs/unlambda/


// This is a specification for a modified Unlambda syntax, produced by the
// accompanying lexer (lexer.sed).



module UNLAMBDA-SYNTAX
   syntax Fun ::= Atom         // atomic function
              |   Apply Fun Fun  // apply function to function

   syntax Apply ::= ">"       // apply token (`)

   syntax Atom ::= "k"         // "constant generator"
               |   "s"         // "substitution"
               |   "i"         // "identity"
               |   "v"         // "void"
               |   "c"         // "call with current continuation"
               |   "d"         // "delay"
               |   "." Int [strict]     // "print"
               |   "r"         // "carriage return"
               |   "e"         // "exit"
               |   "@"         // "read"
               |   "?" Int [strict]    // "compare character read"
               |   "|"         // "reprint character read"
      
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
//      <left> .Map </left> // left child pointers
//      <right> .Map </right> // right child pointers
      <mode> 0 </mode>  // 0 = init, 1 = queue, 2 = eval
      <loc> 0 </loc>   // location of current eval
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

  
  rule [StartTraversal]:
    <mode> 2 => 3 </mode>
    <loc> _ => 1 </loc>
    <status>... 1 |-> (_ => 0) ...</status>

  rule [TraverseTerminal]:
    <mode> 3 => 4 </mode>
    <loc> L:Int => P </loc>
    <tree>... L |-> X:Atom ...</tree>
    <parent>... L |-> P:Int ...</parent>
    <status>... L |-> (0 => 2) ...</status>

  rule [TraverseLeftChild]:
    <mode> 3 </mode>
    <loc> L:Int => C </loc>
    <tree>... L |-> Z:Apply ...</tree>
    <child>... N:Int |-> C:Int ...</child>
   when N ==Int -1 *Int L

  rule [TraverseRightChild]:
    <mode> 4 => 3 </mode>
    <loc> L:Int => C </loc>
    <tree>... L |-> Z:Apply ...</tree>
    <child>... L |-> C:Int ...</child>
    <status>... L |-> (0 => 1) ...</status>
    
  rule [TraverseNonterminal]:
    <mode> 4 </mode>
    <loc> L:Int => P </loc>
    <tree>... L |-> Z:Apply ...</tree>
    <parent>... L |-> P:Int ...</parent>
    <status>... L |-> (1 => 2) ...</status>
  


  
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
