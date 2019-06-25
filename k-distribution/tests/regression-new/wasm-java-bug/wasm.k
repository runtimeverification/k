require "data.k"

module WASM
    imports WASM-DATA

    configuration
      <k> $PGM:Stmts </k>
      <valstack> .ValStack </valstack>

    syntax Instr ::= PlainInstr
                   | "(" PlainInstr Instrs ")"
 // ------------------------------------------
    rule <k> ( PI:PlainInstr IS:Instrs ):Instr => IS ~> PI ... </k>

    syntax EmptyStmt
 // ----------------

    syntax Instr ::= EmptyStmt
    syntax Defn  ::= EmptyStmt
    syntax Stmt  ::= Instr | Defn
 // -----------------------------

    syntax EmptyStmts ::= List{EmptyStmt, ""} [klabel(listStmt)]
    syntax Instrs     ::= List{Instr, ""}     [klabel(listStmt)]
    syntax Defns      ::= List{Defn , ""}     [klabel(listStmt)]
    syntax Stmts      ::= List{Stmt , ""}     [klabel(listStmt)]
 // ------------------------------------------------------------

    syntax Instrs ::= EmptyStmts
    syntax Defns  ::= EmptyStmts
    syntax Stmts  ::= Instrs | Defns
 // --------------------------------
    rule          <k> .Stmts          => .       ... </k>
    rule          <k> (S:Stmt .Stmts) => S       ... </k>
    rule [step] : <k> (S:Stmt SS)     => S ~> SS ... </k> requires SS =/=K .Stmts

    syntax PlainInstr ::= IValType "." "const" Int
 // ------------------------------------------------
    rule <k> ITYPE:IValType . const VAL => #chop(< ITYPE > VAL) ... </k>

    syntax PlainInstr ::= IValType "." IBinOp | IValType "." IBinOp Int Int
 // -----------------------------------------------------------------------
    rule <k> ITYPE . BOP:IBinOp => ITYPE . BOP C1 C2 ... </k>
         <valstack> < ITYPE > C2 : < ITYPE > C1 : VALSTACK => VALSTACK </valstack>

    syntax IBinOp ::= "add"
 // -----------------------
    rule <k> ITYPE . add I1 I2 => #chop(< ITYPE > I1 +Int I2) ... </k>
endmodule
