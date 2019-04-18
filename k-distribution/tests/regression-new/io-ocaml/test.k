// Copyright (c) 2013-2019 K Team. All Rights Reserved.
module TEST
  imports INT
  imports STRING
  imports K-IO

syntax KItem ::= open(String, String) | tell(Int) | getc(Int) | read(Int, Int)
syntax KItem ::= close(Int) | seek(Int, K) [strict(2)] | putc(Int, Int) | write(Int, String)
syntax KItem ::= system(String) | mkstemp(String, String)

syntax KItem ::= assertEqual(K, K)

syntax KResult ::= Int | String | IOError

syntax KItem ::= K "-" K [strict]

rule I1:Int - I2:Int => I1 -Int I2

rule open(S1:String, S2:String) => #open(S1, S2)
rule tell(I:Int) => #tell(I)
rule getc(I:Int) => #getc(I)
rule read(I1:Int, I2:Int) => #read(I1, I2)
rule close(I:Int) => #close(I)
rule seek(I1:Int, I2:Int) => #seek(I1, I2)
rule putc(I1:Int, I2:Int) => #putc(I1, I2)
rule write(I:Int, S:String) => #write(I, S)
rule system(S:String) => #system(S)
rule mkstemp(Prefix:String, Suffix:String) => #mkstemp(Prefix, Suffix)
rule #tempFile(Path:String, Fd:Int) => #close(Fd) ~> #remove(Path)

endmodule
