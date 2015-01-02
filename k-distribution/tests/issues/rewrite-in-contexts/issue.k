// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module ISSUE
   syntax KItem ::= foo(K) | bar(K)
   rule foo(K:K) => bar(K) ~> foo(HOLE) [heat]
   rule K:K ~> foo(HOLE) => foo(K) [cool]
endmodule

