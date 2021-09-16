module TEST-SYNTAX
  imports INT-SYNTAX
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT
  imports BOOL

  configuration <k> split($PGM:Int) </k>
  syntax Int ::= split(Int)  [function, functional]

  rule  split(V:Int)
        =>
          (
            (
              {true #Equals (V >=Int 0)}
              #And V
            )
            #Or
            (
              {false #Equals (V >=Int 0)}
              #And (V +Int 1)
            )
          )
    [label(xyzzy)]

endmodule
