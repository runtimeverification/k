module TEST
 imports DOMAINS

 configuration <k> $PGM:K </k>

 syntax HexWord ::= r"0x[0-9a-fA-F]*"                  [token, avoid]
 syntax String  ::= #parseHexWordString ( HexWord ) [function, functional, hook(STRING.token2string)]
 syntax Int     ::= #parseHex           ( String )  [function]
                   | HexWord
// --------------------------
 rule #parseHex(S) => 0                                        requires S ==String "0x"
 rule #parseHex(S) => String2Base(replaceAll(S, "0x", ""), 16) requires S =/=String "0x"
 rule HEX:HexWord  => #parseHex(#parseHexWordString(HEX)) [macro]

 rule 15 => 16

endmodule
