
module THEKSTUFF
  syntax KItem
  syntax K
  syntax KBott  ::= "[]"           [klabel([])]
  syntax KBott ::= K "~>" K        [klabel(#KSequence), left]
endmodule
