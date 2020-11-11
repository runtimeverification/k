module LEXICAL-SORTS
  syntax Identifier [token]
  syntax IntConstant [token]
  syntax FloatConstant [token]
  syntax CharConstant [token]
  syntax StringLiteral [token]
endmodule

module LEXICAL-SYNTAX
  imports LEXICAL-SORTS

  syntax Identifier ::= r"{IdentifierNonDigit}(({IdentifierNonDigit}|{Digit})*)" [token]
  syntax lexical IdentifierNonDigit = r"{Nondigit}|{UniversalCharacterName}"
  syntax lexical Nondigit = r"[_a-zA-Z]"
  syntax lexical Digit = r"[0-9]"

  syntax lexical UniversalCharacterName = r"(\\\\u{HexQuad})|(\\\\U{HexQuad}{2})"
  syntax lexical HexQuad = r"{HexDigit}{4}"

  syntax IntConstant ::= r"({DecConstant}|{OctConstant}|{HexConstant})({IntSuffix}?)" [token]
  syntax lexical DecConstant = r"{NonzeroDigit}({Digit}*)"
  syntax lexical OctConstant = r"0({OctDigit}*)"
  syntax lexical HexConstant = r"{HexPrefix}({HexDigit}+)"
  syntax lexical HexPrefix = r"0x|0X"
  syntax lexical NonzeroDigit = r"[1-9]"
  syntax lexical OctDigit = r"[0-7]"
  syntax lexical HexDigit = r"[0-9a-fA-F]"
  syntax lexical IntSuffix = r"{UnsignedSuffix}({LongSuffix}?)|{UnsignedSuffix}{LongLongSuffix}|{LongSuffix}({UnsignedSuffix}?)|{LongLongSuffix}({UnsignedSuffix}?)"
  syntax lexical UnsignedSuffix = r"[uU]"
  syntax lexical LongSuffix = r"[lL]"
  syntax lexical LongLongSuffix = r"ll|LL"

  syntax FloatConstant ::= r"{DecFloatConstant}|{HexFloatConstant}" [token]
  syntax lexical DecFloatConstant = r"{FractionalConstant}({ExponentPart}?)({FloatSuffix}?)|{DigitSeq}{ExponentPart}({FloatSuffix}?)"
  syntax lexical HexFloatConstant = r"{HexPrefix}({HexFractionalConstant}|{HexDigitSeq}){BinaryExponentPart}({FloatSuffix}?)"
  syntax lexical FractionalConstant = r"({DigitSeq}?)[.]{DigitSeq}|{DigitSeq}[.]"
  syntax lexical ExponentPart = r"[eE]({Sign}?){DigitSeq}"
  syntax lexical Sign = r"[+-]"
  syntax lexical DigitSeq = r"{Digit}+"
  syntax lexical HexFractionalConstant = r"({HexDigitSeq}?)[.]{HexDigitSeq}|{HexDigitSeq}[.]"
  syntax lexical BinaryExponentPart = r"[pP]({Sign}?){DigitSeq}"
  syntax lexical HexDigitSeq = r"{HexDigit}+"
  syntax lexical FloatSuffix = r"[flFL]"

  syntax CharConstant ::= r"[LuU]?'{CCharSeq}'" [token]
  syntax lexical CCharSeq = r"{CChar}+"
  syntax lexical CChar = r"[^'\\n\\\\]|{EscapeSeq}"
  syntax lexical EscapeSeq = r"{SimpleEscapeSeq}|{OctEscapeSeq}|{HexEscapeSeq}|{UniversalCharacterName}"
  syntax lexical SimpleEscapeSeq = r"\\\\['\\\"?\\\\abfnrtv]"
  syntax lexical OctEscapeSeq = r"\\\\{OctDigit}{1,3}"
  syntax lexical HexEscapeSeq = r"\\\\x{HexDigit}+"

  syntax StringLiteral ::= r"{EncodingPrefix}?\\\"{SCharSeq}?\\\"" [token]
  syntax lexical EncodingPrefix = r"u8|[uUL]"
  syntax lexical SCharSeq = r"{SChar}+"
  syntax lexical SChar = r"[^\\\"\\n\\\\]|{EscapeSeq}"
endmodule

module LEXICAL
  imports LEXICAL-SORTS

endmodule
