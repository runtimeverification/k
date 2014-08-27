// Copyright (c) 2014 K Team. All Rights Reserved.
require "modules/verification_lemmas.k"
require "kernelc-syntax.k"
require "kernelc-semantics.k"
require "patterns/list_pattern.k"
require "patterns/tree_pattern.k"

module KERNELC
  imports KERNELC-SYNTAX
  imports KERNELC-SEMANTICS
  imports LIST-PATTERN
  imports TREE-PATTERN
  imports VERIFICATION_LEMMAS

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

      <in stream="stdin"> .List </in>
      <out stream="stdout"> .List </out>
    </config>


  /*
   * KernelC results
   */
  syntax KResult ::= EvaluatedExpression
endmodule
