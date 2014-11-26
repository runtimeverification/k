// Copyright (c) 2014 K Team. All Rights Reserved.

DEF: null -> null
module TEST
  syntax Exp ::=

  rule A:Exp => A:Exp ensures A:Exp
  rule A:Exp => A:Exp requires A:Exp ensures A:Exp
  rule A:Exp => A:Exp requires A:Exp

endmodule