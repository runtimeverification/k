// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module UNION-SYNTAX
  imports INT

  syntax Ints ::= List{Int,""}
  syntax Pgm ::= Ints ";" Ints
endmodule

module UNION
  imports UNION-SYNTAX
  imports DOMAINS

  syntax Set ::= #IntsToSet(Ints) [function, total]
  syntax Set ::= #IntsToSetAux(Ints, Set) [function, total]

  rule #IntsToSet(Is) => #IntsToSetAux(Is, .Set)
  rule #IntsToSetAux(.Ints, S) => S
  rule #IntsToSetAux(I Is, S) => #IntsToSetAux(Is, S)            requires (I in S)
  rule #IntsToSetAux(I Is, S) => #IntsToSetAux(Is, SetItem(I) S) requires notBool(I in S)

  rule <k> I1 ; I2 => #IntsToSet(I1) |Set #IntsToSet(I2) </k>

  configuration <k> $PGM:Pgm </k>
endmodule

