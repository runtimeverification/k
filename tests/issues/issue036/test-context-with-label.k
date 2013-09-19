module TEST-CONTEXT-WITH-LABEL
syntax KLabel ::= "'L" | "'A"
syntax KResult ::= "res" "(" Id ")"
context 'L(HOLE)
rule 'A(_) => res(String2Id("X"))
endmodule
