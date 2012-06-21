// implementation of SKI calculus

module SKI-SYNTAX

   syntax Fun ::= Atom  // atomic function
              | "@" Fun Fun [strict] // apply function to function

   syntax Atom ::= "s" | "k" | "i" | #Id  // S, K, I; or arbitrary function

endmodule

module SKI
  imports SKI-SYNTAX
  configuration <k> $PGM:Fun </k>
  syntax KResult ::= Fun

  // reduction rules
  rule @ i X:Fun => X [anywhere]
  rule @ @ k X:Fun Y:Fun => X [anywhere]
  rule @ @ @ s X:Fun Y:Fun Z:Fun => @ @ X Z @ Y Z [anywhere]

endmodule
