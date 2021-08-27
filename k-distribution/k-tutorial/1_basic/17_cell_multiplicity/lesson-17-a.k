module LESSON-17-A-SYNTAX
  syntax Stmt   ::= "enable" | "increment" | "decrement" | "disable"

  syntax Stmts  ::= List{Stmt, ""}
endmodule

module LESSON-17-A
  imports LESSON-17-A-SYNTAX
  imports INT

  configuration <k> $PGM:Stmts </k>
                <optional multiplicity="?"> 0 </optional>

  rule  <k> .Stmts => . ...</k>

  rule  <k> enable S => S ...</k>
        (.Bag => <optional> 0 </optional>)

  rule  <k> disable S => S ...</k>
        (<optional> _ </optional> => .Bag)

  rule  <k> increment S => S ...</k>
        <optional> X => X +Int 1 </optional>

  rule  <k> decrement S => S ...</k>
        <optional> X => X -Int 1 </optional>
endmodule
