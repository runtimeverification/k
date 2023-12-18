// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module MIN-SPEC
  imports IMP

claim
  <threads><thread>...
    <k>
      if (a <= b) {
        c = a;
      } else {
        c = b;
      }
    =>
      .K
    ...</k>
    <env>...
      a |-> LA:Int
      b |-> LB:Int
      c |-> LC:Int
    ...</env>
  ...</thread></threads>
  <input>
    ListItem ( #buffer ( "\n" ~> . ) )
    ListItem ( "off" )
    ListItem ( #istream ( 0 ) )
  </input>
  <output>
    ListItem ( #ostream ( 1 ) )
    ListItem ( "off" )
    ListItem ( #buffer ( "" ~> . ) )
  </output>
  <store>...
    LA |-> A:Int
    LB |-> B:Int
    LC |-> (_ => minInt(A, B))
  ...</store>

endmodule
