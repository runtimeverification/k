// Copyright (c) 2013-2015 K Team. All Rights Reserved.
/*@
  requires VELOCITY(x) && VELOCITY(y) ;
  ensures \abs(\result - sqR(x,y)) < E_sqv ;
  assigns \nothing ;
  @*/
//double sqv(double x,double y) { return x*x + y*y; }
module SQV-RULE
  rule <threads>
           <thread>...
         <k> sqv(Vx:Float, Vy:Float) => V:Float </k>
             <env> GENV </env>
       ...</thread>
       </threads>
       <store>... STORE ...</store>
       <genv> GENV </genv>
    requires VELOCITY(Vx) andBool VELOCITY(Vy)
     ensures absFloat(V -Float sqR(Vx, Vy)) <=Float E_sqv
endmodule
