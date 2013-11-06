require "../../kernel-cil.k"
require "cd2d-spec.k"
module CD2D
  imports KERNEL-CIL
  imports CD2D-SPEC
  syntax Id ::= Token{"x"} | Token{"y"}
              | Token{"u_x"} | Token{"u_y"}
              | Token{"v_x"} | Token{"v_y"}
endmodule
