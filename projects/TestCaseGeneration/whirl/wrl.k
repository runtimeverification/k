// Implementation of Whirl in K
// Language specification: http://bigzaphod.org/whirl/



// This is a specification for a modified Whirl syntax, produced by the
// accompanying lexer (lexer.sed).





module WRL-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

  syntax Program  ::= "end"
                    | Bit Program

  syntax Bit ::= #Int

endmodule

module WRL
  imports WRL-SYNTAX
  configuration
    <k> $PGM:Program </k>
    <streams>
      <in stream="stdin"> $IN:List </in>
      <out stream="stdout"> .List </out>
    </streams>
    <settings>
      <mode> 0 </mode>              // 0 = init, 1 = eval, 2 = exec instruction
      <progmap> .Map </progmap>     // maps address to program instruction
      <size> 0 </size>              // size of program
      <ip> 0 </ip>                  // instruction pointer

      <memmap> 0 |-> 0 </memmap>       // memory map
      <mp> 0 </mp>                  // memory pointer
      <memtemp> 0 </memtemp>        // temporary memory value

      <ring> 0 </ring>           // ops ring = 0; math ring = 1
      <turn> 0 |-> 0 1 |-> 0 </turn>  // current instruction
      <val> 0 |-> 0 1 |-> 0  </val>   // value
      <dir> 0 |-> 1 1 |-> 1 </dir>    // direction (ccw = 0; cw = 1)

      <parity> false </parity>      // true iff last operation was a regular 0

      <isign> 1 </isign> // sign of input integer
      <ibuff> 0 </ibuff>  // buffer for integer input
      <buff> "" </buff> // buffer for character input
    </settings>
    
   rule X:Bit Y:Program => X ~> Y [seqstrict, structural]

  
   // initializes by writing entire program to progmap
   rule [Init]:
      <k> X:Bit => . ...</k>
      <mode> 0 </mode>
      <progmap>... . => P |-> X . ...</progmap>
      <ip> P:Int => P +Int 1 </ip> [transition]

   // switches to execute mode
   rule [ProgStart]:
      <k> end </k>
      <mode> 0 => 1 </mode>
      <size> _ => S </size>
      <ip> S:Int => 0 </ip>

   rule [ChangeDirection]:
      <mode> 1 </mode>
      <progmap>... P |-> 0 ...</progmap>
      <parity> false => true </parity>
      <ip> P:Int => P +Int 1 </ip>
      <ring> R:Int </ring>
      <dir>... R |-> (D:Int => 1 -Int D) ...</dir>

   rule [Rotate]:
      <mode> 1 </mode>
      <progmap>... P |-> 1 ...</progmap>
      <parity> _ => false </parity>
      <ip> P:Int => P +Int 1 </ip>
      <ring> R:Int </ring>
      <dir>... R |-> D:Int ...</dir>
      <turn>... R |-> (T:Int => (T +Int (D *Int 2) +Int 11) %Int 12) ...</turn>

   rule [Execute]:
      <mode> 1 => 2 </mode>
      <progmap>... P |-> 0 ...</progmap>
      <parity> true => false </parity>
      <ip> P:Int => P +Int 1 </ip>
      <ring> R:Int </ring> 
      <dir>... R |-> (D:Int => 1 -Int D) ...</dir>
      <turn>... R |-> T:Int ...</turn>
 
   rule [AutoTerminate]: // regular program termination without explicit "exit"
      <k> _ => 0 </k>
      <mode> 1 => -2 </mode>
      <ip> P:Int </ip>
      <size> S:Int </size>
    when (P >=Int S) orBool (P <Int 0)




   // Individual instructions
   rule [Noop]: // both rings 0
      <mode> 2 => 3 </mode>
      <ring> R:Int </ring>
      <turn>... R |-> 0 ...</turn>

   rule [Exit]: // ops ring 1
      <k> _ => 0 </k>
      <mode> 2 => -1 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 1 ...</turn>
      <buff> _ => . </buff>

   rule [One]: // ops ring 2
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 2 ...</turn>
      <val>... 0 |-> (_ => 1) ...</val>

   rule [ZeroOps]: // ops ring 3
      <mode> 2 => 10 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 3 ...</turn>

   rule [LoadOps]: // ops ring 4
      <mode> 2 => 11 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 4 ...</turn>

   rule [StoreOps]: // ops ring 5
      <mode> 2 => 12 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 5 ...</turn>

   rule [PAdd]: // ops ring 6
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 6 ...</turn>
      <val>... 0 |-> V:Int ...</val>
      <ip> P:Int => (P +Int V) </ip>

   rule [DAdd]: // ops ring 7
      <mode> 2 => 8 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 7 ...</turn>
      <val>... 0 |-> V:Int ...</val>
      <mp> M:Int => (M +Int V) </mp>
      
   rule [LogicZeroM]: // ops ring 8, memval = 0
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 8 ...</turn>
      <val>... 0 |-> (_ => 0) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> 0 ...</memmap>

   rule [LogicZeroV]: // ops ring 8, value = 0
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 8 ...</turn>
      <val>... 0 |-> 0 ...</val>
 
   rule [LogicNonzero]: // ops ring 8, memval != 0 and value != 0
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 8 ...</turn>
      <val>... 0 |-> (V:Int => 1) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
    when (I =/=Int 0) andBool (V =/=Int 0)

   rule [IfZero]: // ops ring 9, memval = 0
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 9 ...</turn>
      <val>... 0 |-> V:Int ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> 0 ...</memmap>

   rule [IfNonzero]: // ops ring 9, memval != 0
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 9 ...</turn>
      <val>... 0 |-> V:Int ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
      <ip> P:Int => (P +Int V) </ip>
    when (I =/=Int 0)



   rule [IntInput]: // ops ring 10, value == 0 (input)
      <mode> 2 => 20 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 10 ...</turn>
      <val>... 0 |-> 0 ...</val>
      <buff> "" => charString(#fReadByte(0)) </buff>
      <isign> _ => 1 </isign>

   rule [IntInputBuffer]: // use buffered character
      <mode> 2 => 20 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 10 ...</turn>
      <val>... 0 |-> 0 ...</val>
      <buff> S:String </buff>
      <isign> _ => 1 </isign>
    when lengthString(S) >Int 0

   rule [IntInputIgnoreWhitespace]: // ignore intervening whitespace
      <mode> 20 </mode>
      <buff> S:String => charString(#fReadByte(0)) </buff>
    when (S ==String " ") orBool (S ==String "\n") orBool
         (S ==String "\t") orBool (S ==String "\r")

   rule [IntInputNegative]: // negative integer 
      <mode> 20 => 21 </mode>
      <buff> S:String => charString(#fReadByte(0)) </buff>
      <isign> _ => -1 </isign>
    when (S ==String "-")

   rule [IntInputFirstDigit]: // first digit of integer
      <mode> M:Int => 22 </mode>
      <buff> S:String => charString(#fReadByte(0)) </buff>
      <ibuff> _ => asciiString(S) -Int 48 </ibuff>
    when ((M ==Int 20) orBool (M ==Int 21)) andBool
         (asciiString(S) >=Int 48) andBool (asciiString(S) <=Int 57)
  
   rule [IntInputMoreDigits]: // more digits of integer
      <mode> 22 </mode>
      <buff> S:String => charString(#fReadByte(0)) </buff>
      <ibuff> I:Int => (I *Int 10) +Int (asciiString(S) -Int 48) </ibuff>
    when (asciiString(S) >=Int 48) andBool (asciiString(S) <=Int 57)
 
   rule [IntInputEnd]: // end of integer
      <mode> 22 => 3 </mode>
      <buff> S:String </buff>
      <ibuff> I:Int => 0 </ibuff>
      <isign> P:Int </isign>
      <mp> M:Int </mp>
      <memmap>... M |-> (_ => I *Int P) ...</memmap>
    when (asciiString(S) <Int 48) orBool (asciiString(S) >Int 57)

   rule [IntInputEOF]: // end of integer, EOF
      <mode> 22 => 3 </mode>
      <buff> charString(#EOF) </buff>
      <ibuff> I:Int => 0 </ibuff>
      <isign> P:Int </isign>
      <mp> M:Int </mp>
      <memmap>... M |-> (_ => I *Int P) ...</memmap>
    
  
   

   rule [IntOutput]: // ops ring 10, value != 0 (output)
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 10 ...</turn>
      <val>... 0 |-> V:Int ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
      <out>... . => ListItem(I) </out>
    when (V =/=Int 0)


   rule [AscInput]: // ops ring 11, value == 0 (input); append char to buffer
      <mode> 2 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 11 ...</turn>
      <val>... 0 |-> 0 ...</val>
      <buff> "" => charString(#fReadByte(0)) </buff>

   rule [AscInputBuffer]: // use buffered character if exists
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 11 ...</turn>
      <val>... 0 |-> 0 ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> (_ => asciiString(S)) ...</memmap>
      <buff> S:String => "" </buff>
   when lengthString(S:String) >Int 0


   rule [AscOutput]: // ops ring 10, value != 0 (output)
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 11 ...</turn>
      <val>... 0 |-> V:Int ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> C:Int ...</memmap>
      <out>... . => ListItem(charString(C)) </out>
    when (V =/=Int 0)

   

   rule [LoadMath]: // math ring 1
      <mode> 2 => 11 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 1 ...</turn>

   rule [StoreMath]: // math ring 2
      <mode> 2 => 12 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 2 ...</turn>

   rule [Add]: // math ring 3
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 3 ...</turn>
      <val>... 1 |-> (V:Int => (V +Int I)) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>

   rule [Mult]: // math ring 4
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 4 ...</turn>
      <val>... 1 |-> (V:Int => (V *Int I)) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>

   rule [Div]: // math ring 5
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 5 ...</turn>
      <val>... 1 |-> (V:Int => (V /Int I)) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
    when (I =/=Int 0)
  
   rule [DivByZero]: // math ring 5, division by zero
      <k> _ => 1 </k>
      <mode> 2 => -1 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 5 ...</turn>
      <mp> M:Int </mp>
      <memmap>... M |-> 0 ...</memmap>

   rule [ZeroMath]: // math ring 6
      <mode> 2 => 10 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 6 ...</turn>

   rule [LessThanTrue]: // math ring 7
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 7 ...</turn>
      <val>... 1 |-> (V:Int => 1) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
    when (V <Int I)

   rule [LessThanFalse]: // math ring 7
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 7 ...</turn>
      <val>... 1 |-> (V:Int => 0) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
    when (V >=Int I)

   rule [GreaterThanTrue]: // math ring 8
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 8 ...</turn>
      <val>... 1 |-> (V:Int => 1) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
    when (V >Int I)

   rule [GreaterThanFalse]: // math ring 8
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 8 ...</turn>
      <val>... 1 |-> (V:Int => 0) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
    when (V <=Int I)

   rule [EqualsTrue]: // math ring 9
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 9 ...</turn>
      <val>... 1 |-> (V:Int => 1) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
    when (V ==Int I)

   rule [EqualsFalse]: // math ring 9
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 9 ...</turn>
      <val>... 1 |-> (V:Int => 0) ...</val>
      <mp> M:Int </mp>
      <memmap>... M |-> I:Int ...</memmap>
    when (V =/=Int I)

   rule [NotNonzero]: // math ring 10, value != 0
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 10 ...</turn>
      <val>... 1 |-> (V:Int => 0) ...</val>
    when (V =/=Int 0)

   rule [NotZero]: // math ring 10, value = 0
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 10 ...</turn>
      <val>... 1 |-> (0 => 1) ...</val>
 
   rule [Neg]: // math ring 11
      <mode> 2 => 3 </mode>
      <ring> 1 </ring>
      <turn>... 1 |-> 11 ...</turn>
      <val>... 1 |-> (V:Int => (V *Int -1)) ...</val>
      
   


       
      




   // Memory initialization to 0 upon execution of MAdd
 
   rule [MemoryCheck]: // keep existing value
      <mode> 8 => 3 </mode>
      <mp> M:Int </mp>
      <memmap>... M |-> V:Int ...</memmap>
 
   rule [MemoryInit]: // add default value of 0 to new memory position
      <mode> 8 => 3 </mode>
      <mp> M:Int </mp>
      <memmap> R:Map (. => M |-> 0) </memmap>
    when notBool(M in keys(R))

   
  

   // Common operations between rings
   rule [Zero]: // zero for both rings
      <mode> 10 => 3 </mode>
      <ring> R:Int </ring>
      <val>... R |-> (_ => 0) ...</val>

   rule [Load]: // load for both rings
      <mode> 11 => 3 </mode>
      <ring> R:Int </ring>
      <val>... R |-> (_ => V) ...</val>
      <memmap>... M |-> V:Int ...</memmap>
      <mp> M:Int </mp>

   rule [Store]: // store for both rings
      <mode> 12 => 3 </mode>
      <ring> R:Int </ring>
      <val>... R |-> V:Int ...</val>
      <memmap>... M |-> (_ => V) ...</memmap>
      <mp> M:Int </mp>
      
   

   // Go back to execute mode
   rule [ResumeExecute]:
      <mode> 3 => 1 </mode>
      <ring> R:Int => 1 -Int R </ring>

endmodule
