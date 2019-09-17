// Copyright (c) 2013-2019 K Team. All Rights Reserved.
module TEST
  imports INT
  imports STRING
  imports K-IO

syntax KItem ::= open(String, String) | tell(Int) | getc(Int) | read(Int, Int)
syntax KItem ::= close(Int) | seek(Int, KItem) [strict(2)] | putc(Int, Int) | write(Int, String)
syntax KItem ::= system(String) | mkstemp(String, String) | remove(String)

syntax KItem ::= assertEqual(K, K)

syntax KResult ::= Int | String | IOError

syntax KItem ::= KItem "-" KItem [strict]

rule I1:Int - I2:Int => I1 -Int I2

rule open(S1:String, S2:String) => #open(S1, S2)
rule tell(I:Int) => #tell(I)
rule getc(I:Int) => #getc(I)
rule read(I1:Int, I2:Int) => #read(I1, I2)
rule close(I:Int) => #close(I)
rule seek(I1:Int, I2:Int) => #seek(I1, I2)
rule putc(I1:Int, I2:Int) => #putc(I1, I2)
rule write(I:Int, S:String) => #write(I, S)

// 2
rule system(S:String) => #system(S)

// 3
rule remove(S:String) => #remove(S)
rule mkstemp(Prefix:String, Suffix:String) => #mkstemp(Prefix, Suffix)
rule #tempFile(Path:String, Fd:Int) => #write(Fd, "abc") ~> close(Fd) ~> open(Path, "r") ~> remove(Path)
rule Fd:Int ~> remove(Path) => #read(Fd, 3) ~> Fd ~> remove(Path)
rule "abc" ~> Fd:Int ~> remove(Path) => #close(Fd) ~> remove(Path)

// 4
syntax KItem ::= "orr"
rule orr => #open("../io-java/1.test", "r") ~> orr
rule Fd:Int ~> orr => #read(Fd, 4) ~> Fd:Int ~> orr
rule S1:String              ~> Fd:Int ~> orr => S1       ~> #read(Fd, 100) ~> Fd:Int ~> orr
rule S1:String ~> S2:String ~> Fd:Int ~> orr => S1 ~> S2 ~> #read(Fd, 100)

endmodule
