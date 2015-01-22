// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module RULES
  rule
    <k>
    return (x * x + y * y => V:Float);
    </k>
    <state>...
      x |-> X:Float
      y |-> Y:Float
    ...</state>
  requires -1200.0 <=Float X <=Float 1200.0 andBool -1200.0 <=Float Y <=Float 1200.0
  ensures -0x1.p-30 <=Float V -Float (X *Float X +Float Y *Float Y) <=Float 0x1.p-30
endmodule

