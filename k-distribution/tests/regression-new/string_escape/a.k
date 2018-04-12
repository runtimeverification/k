module A
    imports DOMAINS
    imports STRING-BUFFER
    syntax String ::= unescape(String) [function]
                    | unescape(String, Int, StringBuffer) [function, klabel(unescapeAux)]
 // -------------------------------------------------------------------------------------
    rule unescape(S) => unescape(S, 1, .StringBuffer)
    rule unescape(S, IDX, SB) => unescape(S, IDX +Int 1, SB +String substrString(S, IDX, IDX +Int 1))
      requires IDX <Int lengthString(S) -Int 1 andBool substrString(S, IDX, IDX +Int 1) =/=K "\\"
    rule unescape(S, IDX, SB) => unescape(S, IDX +Int 3, SB +String chrChar(String2Base(substrString(S, IDX +Int 1, IDX +Int 3), 16)))
      requires IDX <Int lengthString(S) -Int 1 andBool substrString(S, IDX, IDX +Int 1) ==K "\\"
    rule unescape(S, IDX, SB) => StringBuffer2String(SB)
      requires IDX ==Int lengthString(S) -Int 1
endmodule
