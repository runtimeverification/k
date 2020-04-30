module A-SPEC
imports A

rule <k> validateSignatures(0, N, Keys, Signatures) => . ... </k>
requires N >=Int 0
 andBool forall(x, 0, N, sign(SALT, Keys[x]) ==Int Signatures[x])

rule <k> validateSignatures(I, N, Keys, Signatures) => . ... </k>
requires 0 <=Int I andBool I <=Int N
 andBool forall(x, I, N, sign(SALT, Keys[x]) ==Int Signatures[x])

endmodule
