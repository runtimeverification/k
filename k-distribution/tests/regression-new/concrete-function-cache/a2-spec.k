module A2-SPEC

imports A

rule [s2]:
<k> begin(bar1(X)) => end(bar3(X)) </k>
requires X <Int 0

endmodule
