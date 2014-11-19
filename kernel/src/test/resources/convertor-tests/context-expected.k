// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax Exp ::= Exp "+" Exp
  Bubble(context,_ + HOLE requires true,[])
  Bubble(context,HOLE + _,[])
endmodule
