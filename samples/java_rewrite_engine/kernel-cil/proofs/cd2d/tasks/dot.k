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
	     <k> return (u_x*v_x + u_y * v_y => V:Float); </k>
	     <env> u_x |-> Lux:Int u_y |-> Luy:Int 
                   v_x |-> Lvx:Int v_y |-> Lvy:Int </env>
	   ...</thread>
       </threads>
       <store> Lux |-> Vux:Float Luy |-> Vuy:Float
               Lvx |-> Vvx:Float Lvy |-> Vvy:Float </store>
    requires DISTANCE(Vux) andBool DISTANCE(Vuy) andBool
             VELOCITY(Vvx) andBool VELOCITY(Vvy)
     ensures absFloat(V -Float dotR(Vux, Vuy, Vvx, Vvy)) <=Float E_dot
endmodule
