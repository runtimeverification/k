module LESSON-16-B-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX
  imports STRING-SYNTAX

  syntax Trace  ::= "@trace"
  syntax Exp    ::= Id "(" ")" | Int | String | Trace
  syntax Stmt   ::= "return" Exp ";" [strict]
  syntax Decl   ::= "fun" Id "(" ")" "{" Stmt "}"
  syntax Pgm    ::= List{Decl, ""}
  syntax Id     ::= "main" [token]
endmodule

module LESSON-16-B
  imports LESSON-16-B-SYNTAX
  imports BOOL
  imports LIST
  imports ID
  imports STRING

  configuration <T>
                  <k> $PGM:Pgm ~> main () </k>
                  <functions> .Map </functions>
                  <fstack> .List </fstack>
                </T>

  rule  <k> D:Decl P:Pgm => D ~> P ...</k>
  rule  <k> .Pgm => . ...</k>

  rule  <k> fun X:Id () { S } => . ...</k>
        <functions>... .Map => X |-> S ...</functions>

  syntax KItem  ::= stackFrame(K, Id)
  rule  <k> X:Id () ~> K => S </k>
        <functions>... X |-> S ...</functions>
        <fstack> .List => ListItem(stackFrame(K, X)) ...</fstack>

  rule  <k> return I:Int ; ~> _ => I ~> K </k>
        <fstack> ListItem(stackFrame(K, _)) => .List ...</fstack>

  rule  <k> return S:String ; ~> _ => S ~> K </k>
        <fstack> ListItem(stackFrame(K, _)) => .List ...</fstack>

  rule  <k> return @trace ; ~> _ => printStackTrace(ListItem(stackFrame(K, X)) L) ~> K </k>
        <fstack> ListItem(stackFrame(K, X)) L:List => L </fstack>

  syntax String ::= printStackTrace(List) [function]
  rule printStackTrace(.List) => ""
  rule printStackTrace(ListItem(stackFrame(_, X)) L:List) => Id2String(X) +String " < " +String printStackTrace(L)

  syntax Bool ::= isKResult(K) [function, symbol]
  rule isKResult(_:Int) => true
  rule isKResult(_:String) => true
  rule isKResult(_:Trace) => true
  rule isKResult(_) => false [owise]
endmodule
