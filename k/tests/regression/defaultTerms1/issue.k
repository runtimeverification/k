// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module ISSUE
  configuration <T>
                  <thread multiplicity="*">
                        <k> $PGM:K </k>
                        <holds> .Map </holds>
                  </thread>
        </T>

  syntax KItem ::= "spawn"

  rule <k> spawn => . ...</k>
       (. =>
            <thread>
              ...
              <k> .K </k>
            </thread>
           )

  rule <k> spawn => . ...</k>
       (. =>
            <thread>
              <k> .K </k>
              ...
            </thread>
           )

  rule <k> spawn => . ...</k>
       (. =>
            <thread>
              ...
              <k> .K </k>
              ...
            </thread>
           )
endmodule
