module EXAMPLE-SYNTAX
  syntax Exp ::= Int | Id "=" Exp [prec 20]
  syntax Exps ::= List{Exp,","} [strict]
  syntax Stmt ::= Exps ";" [prec 30 strict]
  syntax Stmts ::= Stmt | Stmts Stmts [prec 70 gather(E e)]
  syntax Pgm ::= Stmts
end module

module EXAMPLE 
  imports EXAMPLE-SYNTAX

  syntax KResult ::= Int

  configuration <T> <k> $PGM:Pgm </k> </T>

  rule <k> (I:Int ; ~> J:Int ;) => (I +Int J) ; ...</k>
  rule X:Id = I:Int => I
  rule Ss:Stmts Ss':Stmts => Ss ~> Ss' [structural]
end module
