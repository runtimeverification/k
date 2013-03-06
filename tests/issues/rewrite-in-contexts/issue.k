module ISSUE
   syntax K ::= foo(K) | bar(K)
   rule foo(K:K) => bar(K) ~> foo(HOLE) [heat]
   rule K:K ~> foo(HOLE) => foo(K) [cool]
endmodule

