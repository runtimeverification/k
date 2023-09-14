module MINI-KEVM
    imports INT
    imports BOOL
    imports BYTES
    imports K-EQUAL

    configuration
        <k> $PGM:KItem </k>
        <id> 0 </id>
        <accounts>
          <account multiplicity="*" type="Map">
            <acctID> 0 </acctID>
            <storage> .Map </storage>
            <origStorage> .Map </origStorage>
          </account>
        </accounts>

    syntax KItem ::= "a" | "b"
    rule <k> a => b ... </k>

    // Words

    syntax Int ::= "pow160" [alias]
                 | "pow256" [alias]
    rule pow160 => 1461501637330902918203684832716283019655932542976
    rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936

    syntax Bool ::= #rangeUInt ( Int , Int ) [alias]
    rule #rangeUInt(160, X) => 0 <=Int X andBool X <Int pow160
    rule #rangeUInt(256, X) => 0 <=Int X andBool X <Int pow256

    syntax Int ::= chop ( Int ) [function, total, smtlib(chop)]
    rule chop(X) => X modInt pow256 [concrete, smt-lemma]

    syntax Int ::= Int "+Word" Int [function, total]
    rule X +Word Y => chop(X +Int Y)

    // Buffers

    syntax Bytes ::= #bufStrict ( Int , Int ) [function]
    syntax Bytes ::= #buf ( Int , Int ) [function, total, smtlib(buf)]

    rule #bufStrict(SIZE, DATA) => #buf(SIZE, DATA)
      requires 0 <=Int DATA andBool DATA <Int (2 ^Int (SIZE *Int 8))

    // Hashed Locations

    syntax IntList ::= List{Int, ""} [klabel(intList), smtlib(intList)]

    syntax Int ::= keccak ( Bytes ) [function, total, no-evaluators, smtlib(keccak)]

    syntax Int ::= #hashedLocation( String , Int , IntList ) [function, klabel(hashLoc), smtlib(hashLoc)]
    rule #hashedLocation(_LANG, BASE, .IntList      ) => BASE
    rule #hashedLocation( LANG, BASE, OFFSET OFFSETS) => #hashedLocation(LANG, #hashedLocation(LANG, BASE, OFFSET .IntList), OFFSETS) requires OFFSETS =/=K .IntList

    rule #hashedLocation("Solidity", BASE, OFFSET .IntList) => keccak(#bufStrict(32, OFFSET) +Bytes #bufStrict(32, BASE))   requires #rangeUInt(256, BASE) andBool #rangeUInt(256, OFFSET) [simplification]

endmodule
