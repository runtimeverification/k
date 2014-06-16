// Copyright (c) 2013-2014 K Team. All Rights Reserved.

/*@
The brainfuck language uses a simple machine model consisting of the program and instruction pointer, as well as an array of at least 30,000 byte cells initialized to zero; a movable data pointer (initialized to point to the leftmost byte of the array); and two streams of bytes for input and output (most often connected to a keyboard and a monitor respectively, and using the ASCII character encoding).
*/

module BF-SYNTAX
  /*@ 
      The syntax of the language consists in eight commands: > < + - . , [ ]
  */ 
  syntax Ignore ::= Token{~[\>\<\+\-\.\,\[\]\ \n\r\t]+}
                   [regex("[^\\>\\<\\+\\-\\.\\,\\[\\]\\ \n\r\t]+"), onlyLabel]
  syntax Instruction  ::= ">" 
  	 	      	| "<" 
			| "+" 
			| "-" 
			| "."
			| "," [onlyLabel]
			| "[" Instructions "]"
			| Ignore

  /*@
      A Brainfuck program consists in a list of commands. Brainfuck ignores all characters except the eight commands +-<>[],. so no special syntax for comments is needed. Unfortunately, because of K parsing issues, we assume that programs contain only the language instructions.
  */
  syntax Instructions ::= List{Instruction,""}
endmodule

module BF
  imports BF-SYNTAX

  /*@
     The configuration of the language contains the K cell for Brainfuck programs, an array cell containing the byte array, a cell ptr for the instruction pointer and I/O streams. 
  */
  configuration <T> 
  		    <k> $PGM:Instructions </k>
		    <array> .Map </array>
		    <ptr> 0 </ptr>
		    <in stream="stdin"> .List </in>
		    <out stream="stdout"> .List </out>
		</T>

  /*@
    Unroll intructions into KList.
  */
  rule I:Instruction Is:Instructions => I ~> Is
  rule .Instructions => .K

  /*@
  Output the byte at the data pointer.
  */
  rule <k> '.(.KList) => .K ...</k>
       <array>... P |-> V:Int ...</array>
       <ptr> P:Int </ptr>
       <out>... .List => ListItem(chrChar(V)) </out>

  /*@
  Input the byte at the data pointer.
  */
  rule <k> '`,(.KList) => .K ...</k>
       <array>... P |-> (_ => V) ...</array>
       <ptr> P:Int </ptr>
       <in> ListItem(V:Int) => .List ...</in>

  /*@
  Increment the data pointer.
  */
  rule <k> > => .K ...</k>
       <ptr> P:Int => (P +Int 1) </ptr>

  /*@
  Decrement the data pointer.
  */
  rule <k> < => .K ...</k>
       <ptr> P:Int => (P -Int 1) </ptr>

  /*@
  Increment the byte at the data pointer
  */
  rule <k> + => .K ...</k>
       <ptr> P:Int </ptr>
       <array>... P |-> (V:Int => (V +Int 1) modInt 256) ...</array>

  /*@
  Decrement the byte at the data pointer
  */
  rule <k> - => .K ...</k>
       <ptr> P:Int </ptr>
       <array>... P |-> (V:Int => (V -Int 1) modInt 256) ...</array>

  /*@
Brainfuck jumps ('[' and ']') are considered to be loops. Whenever the byte at the data pointer is not zero, execute the loops instructions.
  */
  rule <k> [ Is:Instructions ] => Is ~> [Is] ...</k>
       <ptr> P:Int </ptr>
       <array>... P |-> V:Int ...</array> when V =/=Int 0

  rule <k> [ Is:Instructions ] => .K ...</k>
       <ptr> P:Int </ptr>
       <array>... P |-> 0 ...</array>
      
  rule I:Ignore => .K

  rule <ptr> I:Int </ptr>
       <array> M:Map (.Map => I |-> 0) </array> when notBool(I in keys(M)) andBool (I >=Int 0) [structural]
  
endmodule
