// Copyright (c) 2019 K Team. All Rights Reserved.

module TEST
imports DOMAINS

configuration
  <k> $PGM:Exp </k>
  <topCell1 unused="">
     <foo> 0 </foo>
  </topCell1>
  <topCell2>
    <foos unused=""> 1 </foos>
  </topCell2>

syntax Exp ::= "bar" | Int
rule <k> bar => 10 </k>
     <topCell2>
       <foo> 0 </foo>
       ...
     </topCell2>
endmodule
