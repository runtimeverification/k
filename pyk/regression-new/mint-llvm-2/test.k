module TEST
  imports BOOL
  imports MINT

  syntax MInt{64}
  syntax MInt{32}

  syntax MInt{32} ::= m32() [function]
  syntax MInt{64} ::= m64() [function]
  rule m64() => 0p64
  rule m32() => 0p32
endmodule
