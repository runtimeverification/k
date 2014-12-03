// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax Exp
  rule A [sort(Exp)]=>A [sort(Exp)] requires true ensures A [sort(Exp)] []
  rule A [sort(Exp)]=>A [sort(Exp)] requires A [sort(Exp)] ensures true []
  rule A [sort(Exp)]=>A [sort(Exp)] requires A [sort(Exp)] ensures A [sort(Exp)] []
endmodule
