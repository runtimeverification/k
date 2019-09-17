// Copyright (c) 2013-2019 K Team. All Rights Reserved.
module TEST
  imports K-REFLECTION

syntax K ::= parseKAST(String)
syntax K ::= "#noparse"

rule parseKAST(S) => #parseKAST(S)
// messages from different backend can be different so hide it
rule #noParse(_) => #noparse

endmodule
