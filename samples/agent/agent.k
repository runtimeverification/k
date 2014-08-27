// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "exp.k"
require "if.k"
require "lambda.k"
require "mu.k"
require "callcc.k"
require "halt.k"
require "seq.k"
require "io.k"
require "ref.k"
require "while.k"
require "threads.k"
require "agents.k"
require "quote-unquote.k"

module AGENT-SYNTAX
  imports EXP-SYNTAX
  imports LAMBDA-SYNTAX
  imports MU-SYNTAX
  imports CALLCC-SYNTAX
  imports HALT-SYNTAX
  imports IO-SYNTAX
  imports REF-SYNTAX
  imports WHILE-SYNTAX
  imports THREADS-SYNTAX
  imports AGENTS-SYNTAX
  imports QUOTE-UNQUOTE-SYNTAX

//  syntax priorities dref > mul > and > app >  assgn if prnt rndv > spwn while > seq  > lam
  syntax priorities app
                  > dref
                  > mul
                  > and
                  > assgn prnt sndTo sndSyn bcst rndv newAg
                  > if spwn while
                  > seq
                  > lam mu
endmodule

module AGENT
  imports AGENT-SYNTAX
  imports EXP
  imports LAMBDA
  imports MU
  imports CALLCC
  imports HALT
  imports IO
  imports REF
  imports WHILE
  imports THREADS
  imports AGENTS
  imports QUOTE-UNQUOTE

 configuration
    <T>
      <agent multiplicity="*">
          <control>
              <thread multiplicity="*">
                  <k color="green">$PGM:K</k>
                  <holds>.Map</holds>
              </thread>
          </control>
          <busy>.Set</busy>
//          @latex(\\kBR)
          <mem> .Map </mem> <nextLoc> 0 </nextLoc>
          <me>0</me>
          <parent>-1</parent>
      </agent>
//      @latex(\\kBR)
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting>
//      @latex(\\kBR)
      <messages> <message multiplicity="*">
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message> </messages>
      <IO> <in stream="stdin">.List</in> <out stream="stdout">.List</out> </IO>
    </T>
endmodule
