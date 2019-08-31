module MAPACCESSWANTSCAST
  imports DOMAINS

configuration <k> $PGM:K </k> <map> .Map </map>

  syntax Bytes   ::= String | Bytes32
  syntax Bytes32 ::= String | Hash
  syntax Hash    ::= String
  syntax BytesList ::= List{Bytes, ""}

  syntax Bytes ::= BytesList "[" Int "]"                              [function]

  syntax Hash ::= mapGet ( Int ) [function]
  rule [[ mapGet( I ) => MAP[ I ] ]]
    <map> MAP </map>

endmodule
