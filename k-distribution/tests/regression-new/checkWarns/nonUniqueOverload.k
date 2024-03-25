module NONUNIQUEOVERLOAD-SYNTAX
endmodule

module WARNS
  syntax Foo1 ::= Foo2

  syntax Foo1 ::= "foo" Foo1 [overload(foo), unused]
  syntax Foo2 ::= "foo" Foo2 [overload(foo), unused]

  syntax Foo1 ::= "foo" Foo1 Foo1 [overload(foo), unused]
  syntax Foo2 ::= "foo" Foo2 Foo2 [overload(foo), unused]
endmodule

module WASM-REPRO
    syntax EmptyStmt

    syntax Instr ::= EmptyStmt
    syntax Defn  ::= EmptyStmt
    syntax Stmt  ::= Instr | Defn
 // -----------------------------

    syntax EmptyStmts ::= List{EmptyStmt , ""} [overload(listStmt), terminator-symbol(".List{\"listStmt\"}"), unused]
    syntax Instrs     ::= List{Instr     , ""} [overload(listStmt), unused]
    syntax Defns      ::= List{Defn      , ""} [overload(listStmt), unused]
    syntax Stmts      ::= List{Stmt      , ""} [overload(listStmt), unused]
 // -------------------------------------------------------------

    syntax Instrs ::= EmptyStmts
    syntax Defns  ::= EmptyStmts
    syntax Stmts  ::= Instrs | Defns
endmodule

module NOWARNS
  imports DOMAINS
  imports WASM-REPRO

  syntax Exp  ::= Int | Id

  syntax Exps ::= List{Exp, ","} [overload(exps), unused]
  syntax Ids  ::= List{Id, ","}  [overload(exps), unused]

  syntax Exps ::= Ids
endmodule

module NONUNIQUEOVERLOAD
  imports WARNS
  imports NOWARNS
endmodule
