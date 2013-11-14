/*@
  requires VELOCITY(x) && VELOCITY(y) ;
  ensures \abs(\result - sqR(x,y)) < E_sqv ;
  assigns \nothing ;
  @*/
//double sqv(double x,double y) { return x*x + y*y; }
module MAX-RULE
  rule <threads>
           <thread>...
	     <k> max(Vx:Float, Vy:Float) => V:Float </k>
             <env> GENV </env>
	   ...</thread>
       </threads>
       <store>... STORE ...</store>
       <genv> GENV </genv>
     ensures V ==Float dmax(Vx,Vy)
endmodule
