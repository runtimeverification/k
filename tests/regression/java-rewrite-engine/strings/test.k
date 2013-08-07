module TEST

syntax K ::= test(K)
rule <k> test(K) ~> _ => K </k>

endmodule
