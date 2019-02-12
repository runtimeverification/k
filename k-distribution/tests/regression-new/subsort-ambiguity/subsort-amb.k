// Copyright (c) 2019 K Team. All Rights Reserved.

require "domains.k"

module SUBSORT-AMB-SYNTAX
    imports INT
    imports FLOAT

    syntax IValType ::= "i32" | "i64"
    syntax FValType ::= "f32" | "f64"
    syntax  ValType ::= IValType | FValType
 // ---------------------------------------

    syntax Number ::= Int | Float
 // -----------------------------

    syntax IVal ::= "<" IValType ">" Int
    syntax FVal ::= "<" FValType ">" Float
    syntax  Val ::= "<"  ValType ">" Number
                  | IVal | FVal
 // ---------------------------

    syntax Instr ::= "(" IValType "." "const" Int ")"
 // -------------------------------------------------
endmodule

module SUBSORT-AMB
    imports SUBSORT-AMB-SYNTAX

    configuration
      <k> $PGM:Instr </k>

    rule <k> ( ITYPE:IValType . const VAL ) => < ITYPE > VAL ... </k>
endmodule
