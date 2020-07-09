module TEST-SYNTAX

endmodule

module TEST
imports DOMAINS

    syntax EmptyStmt
 // ----------------

    syntax Instr ::= "foo" [unused]
    syntax Defn  ::= "bar" [unused]
 // ----------------------

    syntax Instr ::= EmptyStmt
    syntax Defn  ::= EmptyStmt
    syntax Stmt  ::= Instr | Defn
 // -----------------------------

    syntax EmptyStmts ::= List{EmptyStmt , ""}
    syntax Instrs     ::= List{Instr     , ""}
    syntax Defns      ::= List{Defn      , ""}
    syntax Stmts      ::= List{Stmt      , ""}
 // ------------------------------------------

    syntax Instrs ::= EmptyStmts
    syntax Defns  ::= EmptyStmts
    syntax Stmts  ::= Instrs | Defns
 // --------------------------------

    syntax K ::= sequenceStmts  ( Stmts  ) [function]
               | sequenceDefns  ( Defns  ) [function]
               | sequenceInstrs ( Instrs ) [function]
 // -------------------------------------------------
    rule sequenceStmts(.Stmts) => .
    rule sequenceStmts(S SS  ) => S ~> sequenceStmts(SS)

    rule sequenceDefns(.Defns) => .
    rule sequenceDefns(D DS  ) => D ~> sequenceDefns(DS)

    rule sequenceInstrs(.Instrs) => .
    rule sequenceInstrs(I IS   ) => I ~> sequenceInstrs(IS)

endmodule
