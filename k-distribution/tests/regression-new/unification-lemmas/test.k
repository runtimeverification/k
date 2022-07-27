// Copyright (c) 2020 K Team. All Rights Reserved.

module TEST-SYNTAX
endmodule

module TEST
    imports TEST-SYNTAX
    imports BOOL
    imports INT
    imports MAP
    imports STRING
    imports MAP-SYMBOLIC

    configuration <k> $PGM:KItem </k>

    syntax KItem ::= makeLookup(Int)
    rule makeLookup(B) => lookup(#hash(B))

    syntax Int ::= lookup(Hash) [function, no-evaluators]
                 | #lookupMemory  ( Map , Int ) [function, functional, smtlib(lookupMemory)]
    syntax Int ::= "pow256" [alias] /* 2 ^Int 256 */
    rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936

    syntax KItem ::= runLemma(Int) | doneLemma(Int)
    rule runLemma(T) => doneLemma(T)

    // -------------------------------------------
    syntax IntList ::= List{Int, ""}

    syntax Bool ::= #rangeUInt(Int) [function, no-evaluators]

    syntax Hash ::= #hash(Int)
                  | #hashedLocation( IntList ) [function]

    rule #hashedLocation(       .IntList) => #hash(0)
    rule #hashedLocation(OFFSET .IntList) => #hash(OFFSET)
      requires #rangeUInt(OFFSET)

     rule [#lookupMemory.some]:   #lookupMemory( (KEY |-> VAL:Int) _M, KEY ) => VAL modInt 256
    rule [#lookupMemory.none]:   #lookupMemory(                    M, KEY ) => 0                 requires notBool KEY in_keys(M)
    //Impossible case, for completeness
    rule [#lookupMemory.notInt]: #lookupMemory( (KEY |-> VAL    ) _M, KEY ) => 0                 requires notBool isInt(VAL)

endmodule
