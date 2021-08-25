module LESSON-03-B

  syntax IntConstant ::= r"({DecConstant}|{OctConstant}|{HexConstant})({IntSuffix}?)" [token]
  syntax lexical DecConstant = r"{NonzeroDigit}({Digit}*)"
  syntax lexical OctConstant = r"0({OctDigit}*)"
  syntax lexical HexConstant = r"{HexPrefix}({HexDigit}+)"
  syntax lexical HexPrefix = r"0x|0X"
  syntax lexical NonzeroDigit = r"[1-9]"
  syntax lexical Digit = r"[0-9]"
  syntax lexical OctDigit = r"[0-7]"
  syntax lexical HexDigit = r"[0-9a-fA-F]"
  syntax lexical IntSuffix = r"{UnsignedSuffix}({LongSuffix}?)|{UnsignedSuffix}{LongLongSuffix}|{LongSuffix}({UnsignedSuffix}?)|{LongLongSuffix}({UnsignedSuffix}?)"
  syntax lexical UnsignedSuffix = r"[uU]"
  syntax lexical LongSuffix = r"[lL]"
  syntax lexical LongLongSuffix = r"ll|LL"

endmodule
