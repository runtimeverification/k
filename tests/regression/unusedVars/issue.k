
module ISSUE
  rule A:Id => .
//  rule . => A:Id
  rule .K => .K when fresh(A:Bool)
//  rule .K => .K when fresh(notBool A:Bool)
  rule .K => fresh(A:Bool)
endmodule
