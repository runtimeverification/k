// Copyright (c) 2013-2019 K Team. All Rights Reserved.
module TEST
  imports K-REFLECTION

syntax KItem ::= parseKAST(String)
syntax KItem ::= "#noparse"

rule parseKAST(S) => #parseKAST(S)
// messages from different backend can be different so hide it
rule #noParse(_) => #noparse

endmodule
