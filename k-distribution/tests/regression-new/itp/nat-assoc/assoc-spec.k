// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// CafeOBJ-style proof of addition associativity
// https://pdfs.semanticscholar.org/16b0/a31be7de330027dfffc3c9521d5d4424e4cd.pdf

module ASSOC-SPEC
    imports NAT

    // induction hypothesis:
    rule (I:Nat + J:Nat) + k => I:Nat + (J:Nat + k) [simplification]

    // Prove associativity: (i + j) + k = i +(j + k)
    // by induction on k

    // base case proof for 0:
    claim <k> I:Nat + (J:Nat + z) => (I:Nat + J:Nat) + z </k>

    // proof of induction step for (s k):
    claim <k> (I:Nat + J:Nat) + s(k) => I:Nat + (J:Nat + s(k)) </k>

    // QED {end of proof for associativity of (_+_)}
endmodule
