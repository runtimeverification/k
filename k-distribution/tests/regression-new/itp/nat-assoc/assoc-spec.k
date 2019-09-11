// CafeOBJ-style proof of addition associativity
// https://pdfs.semanticscholar.org/16b0/a31be7de330027dfffc3c9521d5d4424e4cd.pdf

module IH
    imports NAT

    // declaring constants as arbitrary values
    syntax Nat ::= "k" [function]

    // induction hypothesis:
    rule (I:Nat + J:Nat) + k => I:Nat + (J:Nat + k)
endmodule

module ASSOC-SPEC
    imports IH

    // Prove associativity: (i + j) + k = i +(j + k)
    // by induction on k

    // base case proof for 0:
    rule <k> I:Nat + (J:Nat + z) => (I:Nat + J:Nat) + z </k>

    // proof of induction step for (s k):
    rule <k> (I:Nat + J:Nat) + s(k) => I:Nat + (J:Nat + s(k)) </k>

    // QED {end of proof for associativity of (_+_)}
endmodule
