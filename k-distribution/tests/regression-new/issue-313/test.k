// Copyright (c) 2019 K Team. All Rights Reserved.

module TEST
imports DOMAINS

configuration
  <k> $PGM:Int </k>
  <topCell1>
     <foo> 0 </foo>
  </topCell1>
  <topCell2>
    <foos> 1 </foos>
  </topCell2>

syntax Int ::= "bar"
rule <k> bar => 10 </k>
     <topCell2>
       <foo> 0 </foo>
       ...
     </topCell2>
endmodule
