requires "main.k"

module VERIFICATION
    imports MAIN

    rule #range(8, X) => true requires #range(5, X) [smt-lemma, simplification]
endmodule

module TEST-SPEC
    imports VERIFICATION

    claim <k> a => b ... </k>
          <unused> .K </unused>

endmodule
