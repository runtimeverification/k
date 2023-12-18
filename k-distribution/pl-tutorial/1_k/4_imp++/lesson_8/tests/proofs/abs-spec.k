// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module ABS-SPEC
  imports IMP

claim
  <threads><thread>...
    <k>
      if (0 <= a) {
        b = a;
      } else {
        b = 0 + -a;
      }
    =>
      .K
    ...</k>
    <env>...
      a |-> LA:Int
      b |-> LB:Int
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
    LB |-> (_ => absInt(A))
  ...</store>

endmodule
