requires "smt.k"

module SMTLIB2-TEST-DRIVER
  imports Z3
  imports CVC4

  configuration <k> $PGM:SMTLIB2Script </k>
  rule <k> SCRIPT:SMTLIB2Script => Z3CheckSAT(SCRIPT) </k>
  // rule <k> SCRIPT:SMTLIB2Script => CVC4CheckSAT(SCRIPT) </k>
endmodule
