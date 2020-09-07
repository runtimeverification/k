module A1-SPEC

imports A

rule [s1]:
<k> begin(bar1(X)) => end(bar2(X)) </k>
requires X >Int 0 [simplification]

endmodule
