// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module ISSUE

syntax Stmt ::= test(Exp, Stmts, Stmts) [strict(1)]
syntax Stmt ::= "pass"

syntax Stmts ::= List{Stmt,""}

rule S:Stmt Ss::Stmts => S ~> Ss [macro]
rule .Stmts => .K [macro]

syntax Exp ::= Bool | Exp "==" Exp [strict]
syntax KResult ::= Bool

rule B:Bool == B:Bool => true
rule test(true, _, _) => .K

configuration
  <k> test(true == true, pass pass, pass pass) </k>
endmodule

