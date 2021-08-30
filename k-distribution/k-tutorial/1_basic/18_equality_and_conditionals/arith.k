module ARITH-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX

  syntax Id       ::= "main" [token]

  syntax Exp      ::= Int
                    | "(" Exp ")" [bracket]
                    > Id "(" ")" | Id
                    > "-" Exp [seqstrict]
                    > left: Exp "*" Exp [seqstrict]
                    | Exp "/" Exp [seqstrict]
                    > left: Exp "+" Exp [seqstrict]
                    | Exp "-" Exp [seqstrict]

  syntax VarDecl  ::= "int" Id "=" Exp ";" [strict(2)]
  syntax FunDecl  ::= "fun" Id "(" ")" "{" Stmts "}"

  syntax Stmt     ::= Id "=" Exp ";" [strict(2)]
                    | "return" Exp ";" [strict(1)]
                    | "if" "(" Exp ")" "{" Stmt "}" [strict(1)]
                    | VarDecl
        
  syntax Stmts    ::= List{Stmt, ""}

  syntax Pgm      ::= List{FunDecl, ""}
endmodule

module ARITH
  imports ARITH-SYNTAX
  imports INT
  imports BOOL
  imports LIST
  imports MAP
  imports K-EQUAL

  configuration <T>
                  <k color="red"> $PGM:Pgm ~> main () </k>
                  <state>
                    <functions> .Map </functions>
                    <fstack> .List </fstack>
                    <variables> .Map </variables>
                  </state>
                </T>

  rule  <k> Fd:FunDecl P:Pgm => Fd ~> P ...</k>
  rule  <k> .Pgm => . ...</k>

  rule  <k> S:Stmt Ss:Stmts => S ~> Ss ...</k>
  rule  <k> .Stmts => . ...</k>

  rule  <k> fun X:Id () { S } => . ...</k>
        <functions> STATE => STATE [ X <- S ] </functions>

  rule  <k> X:Id () ~> K => S </k>
        <functions>... X |-> S ...</functions>
        <fstack> .List => ListItem(stackFrame(K, Vs)) ...</fstack>
        <variables> Vs => .Map </variables>

  rule  <k> return I:Int ; ~> _ => I ~> K </k>
        <fstack> ListItem(stackFrame(K, Vs)) => .List ...</fstack>
        <variables> _ => Vs </variables>

  rule  <k> int X:Id = I:Int ; => . ...</k>
        <variables> STATE => STATE [ X <- I ] </variables>
        requires notBool X in_keys(STATE)

  rule  <k> X:Id = I:Int ; => . ...</k>
        <variables> STATE => STATE [ X <- I ] </variables>
        requires X in_keys(STATE)

  rule  <k> if ( I:Int ) { S } => #if I =/=K 0 #then S #else . #fi ...</k>

  rule  <k> X:Id => I ...</k>
        <variables>... X |-> I ...</variables>

  rule <k> - N => 0 -Int N ...</k>
  rule <k> N * M => N *Int M ...</k>
  rule <k> N / M => N /Int M ...</k> requires M =/=Int 0
  rule <k> N + M => N +Int M ...</k>
  rule <k> N - M => N -Int M ...</k>

  syntax KItem ::= stackFrame(K, Map)

  syntax Bool ::= isKResult(Exp) [function, symbol]
  rule isKResult(_:Int) => true
  rule isKResult(_) => false [owise]
endmodule
