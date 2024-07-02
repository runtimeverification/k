// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module SUM-SPEC
  imports IMP

claim
  <threads><thread>...
    <k>
      while (!(n <= 0)) {
        sum = sum + n;
        n = n + -1;
      }
    =>
      .K
    ...</k>
    <env>...
      n   |-> LN:Int
      sum |-> LSUM:Int
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
    LN   |-> (N:Int => 0)
    LSUM |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2))
  ...</store>
  <generatedCounter> _ </generatedCounter>
requires N >=Int 0

claim
  <threads><thread>...
    <k>
      int n, sum;
      n = N:Int;
      sum = 0;
      while (!(n <= 0)) {
        sum = sum + n;
        n = n + -1;
      }
    =>
      .K
    ...</k>
    <env>
      .Map
    =>
      n   |-> ?LN:Int
      sum |-> ?LSUM:Int
    </env>
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
  <store>
    .Map
  =>
    ?LN   |-> 0
    ?LSUM |-> ((N +Int 1) *Int N /Int 2)
  </store>
  <generatedCounter> C:Int => C +Int 2 </generatedCounter>
requires N >=Int 0
endmodule
