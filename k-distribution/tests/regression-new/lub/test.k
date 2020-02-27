module TEST
  imports DOMAINS

  syntax IntPtr ::= PtrValue
  syntax PtrValue ::= SymLoc
  syntax SymLoc
  syntax IntPtr ::= EncodedPtr
  syntax BitValue ::= EncodedPtr
  syntax Encodable ::= PtrValue
  syntax BitValueOrEncodable ::= BitValue | Encodable

  syntax EncodedPtr ::= encodedPtr(PtrValue)
  syntax Bool ::= sameBase(IntPtr, IntPtr) [function]
  rule sameBase(_, (encodedPtr(S:SymLoc) => S))
endmodule
