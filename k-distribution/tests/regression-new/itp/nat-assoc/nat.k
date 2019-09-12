// CafeOBJ-style proof of addition associativity
// https://pdfs.semanticscholar.org/16b0/a31be7de330027dfffc3c9521d5d4424e4cd.pdf

module NAT-SYNTAX
    syntax Nat ::= "z"
                 | s(Nat)
                 | Nat "+" Nat [function]
endmodule

module NAT
    imports NAT-SYNTAX

    configuration <T>
      <k> $PGM:Nat </k>
    </T>

    rule N:Nat + z => N
    rule N:Nat + s(M) => s(N + M)
endmodule
