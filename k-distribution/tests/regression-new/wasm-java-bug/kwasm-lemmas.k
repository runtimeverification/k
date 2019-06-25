module KWASM-LEMMAS
    imports WASM

    rule #chop(< ITYPE:IValType > N) => < ITYPE > N
      requires #inUnsignedRange(ITYPE, N)
    rule #chop(< ITYPE > N) => < ITYPE > #unsigned(ITYPE, N)
      requires #inSignedRange (ITYPE, N)

    syntax Bool ::= #inUnsignedRange (IValType, Int) [function]
    syntax Bool ::= #inSignedRange   (IValType, Int) [function]
 // -----------------------------------------------------------
    rule #inUnsignedRange (ITYPE, I) => 0                 <=Int I andBool I <Int #pow (ITYPE)
    rule #inSignedRange   (ITYPE, I) => #minSigned(ITYPE) <=Int I andBool I <Int #pow1(ITYPE)

    syntax Int ::= #minSigned  ( IValType ) [function]
 // --------------------------------------------------
    rule #minSigned(ITYPE) => 0 -Int #pow1(ITYPE)
endmodule
