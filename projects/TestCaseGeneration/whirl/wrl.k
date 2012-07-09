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
    <mode> 0 </mode>              // 0 = init, 1 = execute
    <progmap> .Map </progmap>     // maps address to program instruction
    <size> 0 </size>              // size of program
    <ip> 0 </ip>                  // instruction pointer

    <memmap> .Map </memmap>       // memory map
    <mp> 0 </mp>                  // memory pointer

    <opsring> 0 </opsring>        // operations ring current instruction
    <opval> 0 </opval>            // operations ring value
    <opdir> 0 </opval>            // operations ring direction (0 = cw)
    <mathring> 0 </mathring>      // math ring current instruction
    <mathval> 0 </mathval>        // math ring value
    <mathdir> 0 </mathdir>        // math ring direction

    <parity> false </parity>      // true iff last operation was a regular 0
    

 //   syntax KResult ::= Program

    rule X:Bit Y:Program => X ~> Y [seqstrict, structural]

  
   rule [Init]:
      <k> X:Bit => . ...</k>
      <out>... . => ListItem(X) </out>
      <mode> 0 </mode>
      <progmap>... . => P |-> X . ...</progmap>
      <ip> P:Int => P +Int 1 </ip> [transition]

   rule [ProgStart]:
      <k> end </k>
      <mode> 0 => 1 </mode>
      <size> _ => S </size>
      <parity> _ => false </parity>
      <ip> S:Int => 0 </ip>

//   rule [Execute]:
//    <k> end </k>

endmodule
