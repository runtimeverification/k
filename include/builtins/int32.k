// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module INT32

syntax Int32 ::= Token{"[0-9]+i32"}
               | Int32 "+Int32" Int32 [function, left, smtlib(+), latex({#1}\mathrel{+_{\scriptstyle\it Int32}}{#2}), hook(#INT32:_+Int32_)]

endmodule
