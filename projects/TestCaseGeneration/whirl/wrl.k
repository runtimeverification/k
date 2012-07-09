// Implementation of Whirl of K
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

      <memmap> 0 |-> 0 .  </memmap>       // memory map
      <mp> 0 </mp>                  // memory pointer

      <ring> 0 </ring>           // ops ring = 0; math ring = 1
      <turn> 0 |-> 0 1 |-> 0 </turn>  // current instruction
      <val> 0 |-> 0 1 |-> 0  </val>   // value
      <dir> 0 |-> 1 1 |-> 1 </val>    // direction (ccw = 0; cw = 1)

      <parity> false </parity>      // true iff last operation was a regular 0
    </settings>
    

 //   syntax KResult ::= Program

    rule X:Bit Y:Program => X ~> Y [seqstrict, structural]

  
   // initializes by writing entire program to progmap
   rule [Init]:
      <k> X:Bit => . ...</k>
//      <out>... . => ListItem(X) </out>
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
      <turn>... R |-> (T:Int => (T +Int (2 *Int D) -Int 1) %Int 12) ...</turn>

   rule [Execute]:
      <mode> 1 => 2 </mode>
      <progmap>... P |-> 0 ...</progmap>
      <parity> true => false </parity>
      <ip> P:Int => P +Int 1 </ip>
      <ring> R:Int </ring> 
      <dir>... R |-> (D:Int => 1 -Int D) ...</dir>
 


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
      
   rule [LogicZeroM]: // ops ring 8
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 8 ...</turn>
      <val>... 0 |-> (_ => 0) ...</val>
      <memmap>... M |-> 0 ...</memmap>
      <mp> M:Int </mp>

   rule [LogicZeroV]: // ops ring 8
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 8 ...</turn>
      <val>... 0 |-> 0 ...</val>
 
   rule [LogicNonzero]: // ops ring 8
      <mode> 2 => 3 </mode>
      <ring> 0 </ring>
      <turn>... 0 |-> 8 ...</turn>
      <val>... 0 |-> (V:Int => 1) ...</val>
      <memmap>... M |-> I:Int ...</memmap>
      <mp> M:Int </mp>
      when (I =/=Int 0) andBool (V =/=Int 0)


       // TODO: Implement more individual instructions  



   // Memory initialization to 0 upon execution of MAdd

  // TODO: does this always work?
  //       how to prevent [MemoryInit] from running if [MemoryCheck] matches?

   rule [MemoryCheck]: // keep existing value in new memory position
      <mode> 8 => 3 </mode>
      <mp> M:Int </mp>
      <memmap>... M |-> _ ...</memmap>
 
   rule [MemoryInit]: // add default value of 0 to new memory position
      <mode> 8 </mode>
      <mp> M:Int </mp>
      <memmap>... . => (M |-> 0) . </memmap>

   
  

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
