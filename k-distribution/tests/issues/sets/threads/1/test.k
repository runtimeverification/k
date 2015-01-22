// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "builtins/set.k"
module TEST
  imports SET
  syntax Exp ::= Int | "spawn"
  syntax Stmt ::=  Exp ";" [strict] | Stmt Stmt

  syntax KResult ::= Int

  configuration <T>
            <threads>
                <thread multiplicity="*">
                    <k> $PGM:Stmt </k>
                    <id> 0 </id>
                </thread>
            </threads>
            <terminated> .MySet </terminated>
        </T>

    rule <thread>...
         <k> spawn => T ...</k>
       ...</thread>
       (. => <thread>...
               <k> .K </k>
               <id> T </id>
             ...</thread>)
    when fresh(T:Int)
    [transition]

   rule I:Int ; => .K
   rule S1:Stmt S2:Stmt => S1 ~> S2

  rule (<thread>...
          <k> . </k>
          <id> T:Int </id>
        ...</thread>
        => .)
       <terminated>... .MySet => MySetItem(T) ...</terminated>
    [transition]

endmodule
