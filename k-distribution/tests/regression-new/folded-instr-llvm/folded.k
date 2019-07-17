// Copyright (c) 2019 K Team. All Rights Reserved.

module FOLDED-SYNTAX
    imports DOMAINS
    syntax EmptyStmt
    syntax Instr ::= EmptyStmt
    syntax Stmt  ::= Instr

    syntax EmptyStmts ::= List{EmptyStmt , ""} [klabel(listStmt)]
    syntax Instrs     ::= List{Instr     , ""} [klabel(listStmt)]
    syntax Stmts      ::= List{Stmt      , ""} [klabel(listStmt)]
    
    syntax Instrs ::= EmptyStmts
    syntax Stmts  ::= Instrs

    syntax Instr ::= PInstr
                   | "(" PInstr Instrs ")"
                   | "(" PInstr        ")" [prefer]
    syntax PInstr ::= aaa ( Int )
endmodule

module FOLDED
    imports FOLDED-SYNTAX
    configuration
      <k> $PGM:Stmts </k>

    rule          <k> .Stmts          => .       ... </k>
    rule          <k> (S:Stmt .Stmts) => S       ... </k>
    rule [step] : <k> (S:Stmt SS)     => S ~> SS ... </k> requires SS =/=K .Stmts

    rule <k> ( I:PInstr IS:Instrs ):Instr => IS ~> I ... </k>
    rule <k> ( I:PInstr           ):Instr =>       I ... </k>

    rule <k> aaa ( I ) => . ... </k>
endmodule
