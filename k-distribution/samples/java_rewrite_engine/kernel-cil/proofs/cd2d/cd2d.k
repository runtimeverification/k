// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "../../kernel-cil.k"
require "cd2d-spec.k"
module CD2D
  imports KERNEL-CIL
  imports CD2D-SPEC
  syntax Id ::= Token{"sqs"} | Token{"sqv"} | Token{"dot"} | Token{"tau_vv"}
              | Token{"max"} | Token{"min"} | Token{"horizontal_los"}

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      //<k color="green"> ($PGM:Stmts ~> execute) </k>
                      <k color="green"> $PGM:K ~> setGEnv </k>
                      //<br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                      </control>
                      //<br/>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>
                  //<br/>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan"> .Set </busy>
                  <terminated color="red"> .Set </terminated>
                  //<br/>
                  <in color="magenta" > .List </in>
                  <out color="brown" > .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>

  syntax KItem ::= "setGEnv"
  rule <k> setGEnv => . </k>
       <env> Env:Map </env>
       <genv> .Map => Env </genv>   [structural]
endmodule
