// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*@  requires DISTANCE(s_x) && DISTANCE(s_y);
     requires VELOCITY(v_x) && VELOCITY(v_y);
      ensures  \abs(\result - tauR(s_x, s_y, v_x, v_y,0.0,T)) <= E_tau ;
  @*/
/*
double tau_vv(double s_x, double s_y, double v_x, double v_y){
  return min(max(0.0, - dot(s_x,s_y, v_x, v_y)), T*sqv(v_x, v_y));
}
*/

module TAU-RULE
  rule <threads>
           <thread>...
         <k> tau_vv(Sx:Float, Sy:Float, Vx:Float, Vy:Float) => V:Float </k>
             <env> GENV </env>
       ...</thread>
       </threads>
       <store>... STORE ...</store>
       <genv> GENV </genv>
    requires DISTANCE(Sx) andBool DISTANCE(Sy)
     andBool VELOCITY(Vx) andBool VELOCITY(Vy)
     ensures absFloat(V -Float tauR(Sx, Sy, Vx, Vy, 0.0, 300.0)) <=Float E_tau
endmodule


