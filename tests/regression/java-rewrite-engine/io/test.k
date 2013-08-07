module TEST

syntax K ::= open(String, String) | tell(Int) | getc(Int) | read(Int, Int)

syntax K ::= assertEqual(K, K) [strict]

syntax KResult ::= Int | String | TCPError

rule open(S1, S2) => #open(S1, S2)
rule tell(I) => #tell(I)
rule getc(I) => #getc(I)
rule read(I1, I2) => #read(I1, I2)

rule assertEqual(K, K) => .

endmodule
