module TEST
  imports INT
  imports K-REFLECTION

syntax A ::= "a1" A
           | "a2" A
           | "a1" [klabel(b1), symbol]
           | "a2" [klabel(a2), symbol]

rule a1 => #unparseKORE(a1)
rule a2 => #unparseKORE(a2)
rule a1 A => #unparseKORE(a1 A)
endmodule

