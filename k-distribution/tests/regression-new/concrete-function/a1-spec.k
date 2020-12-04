module A1-SPEC

imports A

claim [s1]:
<k> begin(bar1(X)) => end(bar2(X)) </k>
requires X >Int 0

endmodule
