// Copyright (c) 2018-2019 K Team. All Rights Reserved.
module TEST-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Stmt  ::= "addContract"   "(" Id ")" ";"
                 | "addFunction"   "(" Id "," Id ")" ";"
                 | "testFunction"  "(" Id "," Id ")" ";"
                 | "testFunction1" "(" Int ")" ";"
                 > Stmt Stmt       [left, format(%1%n%2)]

  syntax Pgm ::= Stmt
endmodule

module TEST
  imports TEST-SYNTAX
  imports DOMAINS

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <nextFunction> 0:Int </nextFunction>
                  <functions color="blue">
                    <function multiplicity = "*" type = "Map">
                      <fId> 0:Int </fId>
                    </function>
                  </functions>
                  <contracts color="orange">
                    <contract multiplicity = "*" type = "Map">
                      <cName> . </cName>
                      <cFunctions> .Map </cFunctions>
                    </contract>
                  </contracts>
                </T>

  rule
    <k> addContract(ContractName:Id); => . ... </k>
    <contracts>
      ...
      (.Bag =>
        <contract>
          <cName> ContractName </cName>
          <cFunctions> .Map </cFunctions>
        </contract>)
      ...
    </contracts>

rule
  <k> addFunction(ContractName:Id, FunctionName:Id); => . ... </k>
    <contracts>
      ...
      <contract>
        <cName> ContractName </cName>
        <cFunctions> ... .Map => FunctionName |-> N ... </cFunctions>
      </contract>
      ...
    </contracts>
    <nextFunction> N => N +Int 1 </nextFunction>
    <functions>
      (.Bag => <function> <fId> N </fId> </function>)
      ...
    </functions>

rule
  <k> testFunction(ContractName:Id, FunctionName:Id); => "done" ... </k>
      <contract>
        <cName> ContractName </cName>
        <cFunctions> ... FunctionName |-> N:Int ... </cFunctions>
      </contract>
      <function> <fId> N </fId> </function>

rule
  S1:Stmt S2:Stmt => S1 ~> S2  [structural]

endmodule
