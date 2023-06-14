// Copyright (c) K Team. All Rights Reserved.
module TEST
  syntax Int ::= r"[\\+-]?[0-9]+" [prefer, token, prec(2), badAtt(10)]
               | Int "+" Int [group(badAttButOkay),badAtt,function]
endmodule
