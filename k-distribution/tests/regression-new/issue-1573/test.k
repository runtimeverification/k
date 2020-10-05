module TEST
  import INT

  syntax IntList ::= List{Int, ""}

  syntax KItem ::= "go" | "fun"

  configuration
    <top>
      <k> go ~> $PGM:K </k>
      <v> .IntList </v>
    </top>

  syntax Int ::= foo(Int) [function]
  rule foo(I) => 10 *Int I

  rule <k> go => .K ... </k>
       <v> _ => 1 </v>

  rule <k> fun => .K ... </k>
       <v> 1 => foo(1) </v>

endmodule
