// Copyright (c) 2014 K Team. All Rights Reserved.

require "kernelC-syntax.k"
require "kernelC-semantics.k"

module KERNELC
  imports KERNELC-SYNTAX
  imports KERNELC-SEMANTICS

  /*
   * KernelC configuration
   */
  configuration
    <config>
      <struct> .Map </struct>
      <fun> .Map </fun>

      <k> $PGM:File ~> main(.Expressions) </k>
      <env> .Map </env>
      <fun-id> String2Id("") </fun-id>
      <stack> .List </stack>

      <heap> .Map </heap>

      <in> .List </in>
      <out> .List </out>
    </config>


  /*
   * KernelC results
   */
  syntax KResult ::= EvaluatedExpression
endmodule

