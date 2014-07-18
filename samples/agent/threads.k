// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "int.k"
require "seq.k"

module THREADS-SYNTAX imports SEQ-SYNTAX
  imports INT-EXP-SYNTAX
  syntax Exp ::= "acquire" Exp     [acq, strict]
             | "release" Exp     [rel, strict]
             | "rendezvous" Exp  [rndv, strict]
             > "spawn" Exp       [spwn]
endmodule

module THREADS
  imports THREADS-SYNTAX
  imports SEQ
  imports INT-EXP
  configuration <thread multiplicity="*">
                  <k> .K </k> <holds> .Map </holds>
                </thread>
                <busy> .Set </busy>
  rule [spawn-thread] :
       <thread>... <k>spawn S
                      => skip ...</k>  ...</thread>
       (. => <thread>...  <k>S</k>  ...</thread>) [transition]

  rule [end-thread] :
       (<thread>...  <k>V:Val</k> <holds>Holds:Map</holds>
        ...</thread> => .) <busy>Busy:Set
                                 => Busy -Set keys(Holds)</busy> [transition]

  rule [free-acquire] :
       <k>acquire V:Val
          => skip ...</k> <holds>... .Map
                                     => V|->0 ...</holds>
       <busy>Busy (.Set
                   => SetItem(V))</busy>
    when notBool(V in Busy:Set) [transition]
  rule [reentrant-acquire] :
       <k>acquire V:Val
          => skip ...</k> <holds>... V|->(N
                                          => N +Int 1) ...</holds>

  rule [reentrant-release] :
       <k>release V:Val
          => skip ...</k> <holds>... V|->(N
                                          => N -Int 1) ...</holds>
    when N >Int 0

  rule [release] :
       <k>release V:Val
          => skip ...</k> <holds>... (V|->0
                                      => .Map) ...</holds>
       <busy>... (SetItem(V)
            => .Set) ...</busy>

  rule [rendezvous] :
       <k>rendezvous V:Val
          => skip ...</k> <k>rendezvous V
                             => skip ...</k>  [transition]
endmodule
