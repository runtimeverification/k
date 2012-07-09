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

      <memmap> .Map </memmap>       // memory map
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
      <turn>... R |-> (T:Int => T +Int (2 *Int D) -Int 1) ...</turn>

   rule [Execute]:
      <mode> 1 => 2 </mode>
      <progmap>... P |-> 0 ...</progmap>
      <parity> true => false </parity>
      <ip> P:Int => P +Int 1 </ip>
      <ring> R:Int </ring> 
      <dir>... R |-> (D:Int => 1 -Int D) ...</dir>
 

    // TODO: Implement individual instructions   


   rule [ResumeExecute]:
      <mode> 3 => 1 </mode>
      <ring> R:Int => 1 -Int R </ring>

endmodule
