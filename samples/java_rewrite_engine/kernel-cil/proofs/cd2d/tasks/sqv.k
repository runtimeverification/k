/*@
  requires VELOCITY(x) && VELOCITY(y) ;
  ensures \abs(\result - sqR(x,y)) < E_sqv ;
  assigns \nothing ;
  @*/
//double sqv(double x,double y) { return x*x + y*y; }
module SQV-RULE
  rule <threads>
           <thread>...
	     <k> return (x*x + y * y => V:Float); </k>
	     <env> x |-> Lx:Int y |-> Ly:Int </env>
	   ...</thread>
       </threads>
       <store> Lx |-> Vx:Float Ly |-> Vy:Float </store>
    requires VELOCITY(Vx) andBool VELOCITY(Vy)
     ensures (-0x1.p-30) <=Float V -Float sqR(Vx, Vy) <=Float 0x1.p-30
endmodule
