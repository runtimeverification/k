// Copyright (c) 2012-2014 K Team. All Rights Reserved.

module ISSUE
  rule A:Id => .
//  rule . => A:Id
  rule .K => .K when fresh(A:Bool)
//  rule .K => .K when fresh(notBool A:Bool)
  rule .K => fresh(A:Bool)
endmodule
