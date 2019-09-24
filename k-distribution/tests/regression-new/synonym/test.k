requires "rat.k"

module TEST
  imports RAT

  syntax Wad = Rat

  syntax Ray = Rat

  configuration <k> $PGM:K </k> <r> 0:Wad </r>

  syntax Wad ::= Wad "+Wad" Wad [function]

  rule 0 => (0 +Wad 0) +Rat 1
  rule R +Wad R => R +Rat R

  syntax Foo ::= foo(Ray)

endmodule
