require "domains.k"

module WASM-DATA
    imports DOMAINS

    syntax #Layout ::= r"\\(;([^;]|(;+([^;\\)])))*;\\)" [token]
                     | r";;[^\\n\\r]*"                  [token]
                     | r"[\\ \\n\\r\\t]"                [token]
 // -----------------------------------------------------------

    syntax IValType ::= "i32" | "i64"
 // ---------------------------------

    syntax Int ::= #pow ( IValType ) [function, smtlib(pow)]
 // --------------------------------------------------------
    rule #pow (i32) => 4294967296
    rule #pow (i64) => 18446744073709551616

    syntax IVal ::= "<" IValType ">" Int [klabel(<_>_)]
    syntax Val  ::= IVal
 // --------------------

    syntax ValStack ::= ".ValStack" | Val ":" ValStack
 // --------------------------------------------------

    syntax Val ::= "undefined"
 // --------------------------

    syntax IVal ::= #chop ( IVal ) [function]
 // -----------------------------------------
    rule #chop(< ITYPE > N) => < ITYPE > (N modInt #pow(ITYPE)) [concrete]
endmodule
