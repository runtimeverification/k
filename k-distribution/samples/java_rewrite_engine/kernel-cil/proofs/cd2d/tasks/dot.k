// Copyright (c) 2013-2015 K Team. All Rights Reserved.
/*@
  requires DISTANCE(u_x) && DISTANCE(u_y);
  requires VELOCITY(v_x) && VELOCITY(v_y);
  ensures \abs(\result - dotR(u_x, u_y, v_x, v_y)) < E_dot ;
  assigns \nothing ;
double dot(double u_x, double u_y, double v_x, double v_y){
  return u_x * v_x + u_y * v_y ;
}
  @*/
module DOT-RULE
  rule <threads>
           <thread>...
         <k> dot(Ux:Float, Uy:Float, Vx:Float, Vy:Float) => V:Float </k>
             <env> GENV </env>
       ...</thread>
       </threads>
       <store>... STORE ...</store>
       <genv> GENV </genv>
    requires DISTANCE(Ux) andBool DISTANCE(Uy)
     andBool VELOCITY(Vx) andBool VELOCITY(Vy)
     ensures absFloat(V -Float dotR(Ux, Uy, Vx, Vy)) <=Float E_dot
endmodule

