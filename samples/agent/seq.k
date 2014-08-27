// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "val.k"
module SEQ-SYNTAX
  syntax Exp ::= "skip"
             >  Exp ";" Exp                  [seq,left, strict(1)]
endmodule

module SEQ
  imports SEQ-SYNTAX
  imports VAL
  syntax Val ::= "skip"
  rule V:Val ; S:K => S [structural]
endmodule
