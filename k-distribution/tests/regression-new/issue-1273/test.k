module TEST
    imports INT
    imports BOOL

    syntax FInt ::= "(" FInt ")"                   [bracket]
                  | FInt ( value: Int , one: Int ) [klabel(FInt), symbol]
 // ---------------------------------------------------------------------

    syntax FInt ::= "1FInt" "(" Int ")"
 // -----------------------------------
    rule 1FInt(ONE) => FInt(ONE, ONE) [macro]

    syntax FInt ::= foo ( FInt ) [function]
 // ---------------------------------------
    rule foo(FI) => 1FInt(one(FI))
endmodule
