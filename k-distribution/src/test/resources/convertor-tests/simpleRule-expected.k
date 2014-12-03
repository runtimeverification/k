// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax Exp
  rule A [sort(Exp)]=>A [sort(Exp)] requires true ensures true []
endmodule
