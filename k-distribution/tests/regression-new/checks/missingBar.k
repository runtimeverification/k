module MISSINGBAR

  syntax Foo ::= foo ()
                 bar ()

  rule foo () => bar ()

endmodule

