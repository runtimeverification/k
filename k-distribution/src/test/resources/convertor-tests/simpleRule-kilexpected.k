// Copyright (c) 2014-2015 K Team. All Rights Reserved.
DEF: null -> null
module TEST
  rule A:Exp => A:Exp requires '_andBool_(#token("Bool", "true")(),, isExp(A:Exp))
  syntax Exp ::=


endmodule

