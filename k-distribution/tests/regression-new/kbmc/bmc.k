module BMC-SYNTAX
  imports DOMAINS-SYNTAX

  syntax KItem ::= "#execute"
                 | "#branchNoChange" | "#branchIncrease"
                 | "#minusOne" | "#addOne"

endmodule

module BMC
  imports BMC-SYNTAX
  imports DOMAINS

  configuration <T>
                  <k> #execute </k>
                  <state> "x" |-> 0 </state>
                </T>

  rule <k> #execute => #branchIncrease ~> #execute ... </k>
       <state> "x" |-> X </state>
    requires X <Int 0

  rule <k> #execute => #branchNoChange ~> #execute ... </k>
       <state> "x" |-> X </state>
    requires 0 <Int X andBool X <=Int 5

  rule <k> #execute => #branchNoChange ~> #execute ... </k>
       <state> "x" |-> X </state>
    requires X >Int 5

  rule <k> #execute => #branchIncrease ~> #execute ... </k>
       <state> "x" |-> X </state>
    requires X >Int 5

  rule <k> #branchNoChange => #minusOne ~> #addOne ...</k>

  rule <k> #branchIncrease => #addOne ...</k>

  rule <k> #minusOne => . ... </k>
       <state> "x" |-> (X => X -Int 1) </state>

  rule <k> #addOne => . ... </k>
       <state> "x" |-> (X => X +Int 1) </state>

endmodule


