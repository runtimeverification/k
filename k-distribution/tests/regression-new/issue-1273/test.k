// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
    imports INT
    imports BOOL

    syntax FInt ::= "(" FInt ")"                   [bracket]
                  | FInt ( value: Int , one: Int ) [symbol(FInt)]
 // ---------------------------------------------------------------------

    syntax FInt ::= "1FInt" "(" Int ")" [macro]
 // -------------------------------------------
    rule 1FInt(ONE) => FInt(ONE, ONE)

    syntax FInt ::= foo ( FInt ) [function]
 // ---------------------------------------
    rule foo(FI) => 1FInt(one(FI))
endmodule
