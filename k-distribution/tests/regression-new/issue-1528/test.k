module TEST
  imports INT

syntax Exp ::= foo(Exp) | bar(Int, Int) | Int

rule foo(0) => bar(!I:Int, !I:Int) ~> #fun(_B => bar(!I:Int, !I:Int))(0)
rule foo(1) => bar(!I:Int, !I:Int) ~> #fun(_B => bar(!I:Int, !I:Int) ~> #fun(_B2 => bar(!I:Int, !I:Int))(0))(0)
rule foo(2) => bar(!I:Int, !J:Int) ~> #fun(_B => bar(!I:Int, !J:Int) ~> #fun(_B2 => bar(!I:Int, !J:Int))(0))(0)

endmodule
