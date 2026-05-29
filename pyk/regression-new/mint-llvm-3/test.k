module TEST
  imports BOOL
  imports MINT

  syntax MInt{64}
  syntax MInt{32}

  syntax KItem ::= foo(MInt{64})

  syntax MInt{64} ::= m64() [function]
  rule m64() => 0p64
  syntax MInt{32} ::= m32() [function]
  rule m32() => 0p32

  rule foo(X) => .K
    requires (X +MInt m64()) <=uMInt (roundMInt(m32()) <<MInt 0p64)

  rule true => foo(0p64)
endmodule
