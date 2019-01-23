// Copyright (c) 2015-2019 K Team. All Rights Reserved.
module ISSUE
  syntax State ::= "thinks" | "hungry" | "eats"

  syntax Stmt ::= "init" "(" Int "," State ")"
                | "check" "(" Int "," State ")"
                | Stmt ";" Stmt [left]
  configuration <k>
                      $PGM:Stmt
                </k>
                <philosophers>
                  <philosopher multiplicity="*">
                    <id> 0 </id>
                    <state> thinks </state>
                  </philosopher>
                </philosophers>
                <out stream="stdout"> .List </out>

  rule St:Stmt ; St1:Stmt => St ~> St1

  rule <k> true => .K ...</k>
       <out>... .List => ListItem("true") </out>

  rule <k> false => .K ...</k>
       <out>... .List => ListItem("false") </out>

  rule <k> check(N,S) => checkBag(B,N,S) ...</k>
       <philosophers> B </philosophers>

  syntax Bool ::= checkBag(Bag,Int,State) [function]
  rule checkBag(B,N,S)
    => <generatedTop> <k>.K</k> <philosophers> B </philosophers>
       </generatedTop> |= idStatePair(S, N)

  rule <k> init(N,S) => .K ...</k>
       (.  => <philosopher> <id> N </id> <state> S </state> </philosopher>)

  syntax KItem ::= idStatePair(State, Int)
  syntax Bool ::= Bag "|=" String [function]
  rule <generatedTop>... <philosophers>... <philosopher>...
         <id> N </id>
         <state> S </state>
       ...</philosopher> ...</philosophers> ...</generatedTop>
       |=
       idStatePair(S, N)
       => true [assoc, comm]

  rule <generatedTop> B </generatedTop> |= K:K => false [owise]


endmodule
