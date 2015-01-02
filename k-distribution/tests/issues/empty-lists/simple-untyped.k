// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module SIMPLE-UNTYPED-SYNTAX

  syntax Start ::= Stmts
  syntax Ids ::= List{Id,","}     [strict, cons("Ids1ListSyn"), hybrid]
  syntax Exps ::=  List{Exp,","}  [cons("Exps1ListSyn")]


  syntax Decl ::= "var" Exps ";"  [cons("Ddecl1VarDeclSyn")]

  syntax Exp ::= Int | Bool | Id | String
                 > Exp "=" Exp    [strict(2), right, cons("Exp1AssignSyn")]

  syntax Stmt ::=  Exp ";"        [strict, cons("Stmt1Stmt2ExpSyn")]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts    [right, cons("Stmts1LstStmtsSyn")]

endmodule






module SIMPLE-UNTYPED
  imports SIMPLE-UNTYPED-SYNTAX

  rule var X:Id = E:Exp; => var X; X = E;

endmodule
