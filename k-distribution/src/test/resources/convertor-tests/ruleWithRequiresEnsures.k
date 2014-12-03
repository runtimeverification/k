// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax Exp

  rule A:Exp => A requires A
  rule A:Exp => A ensures A
  rule A:Exp => A requires A ensures A
endmodule
