/*@
  requires DISTANCE(x) && DISTANCE(y) ;
  ensures \abs(\result - sqR(x,y)) < E_sqs ;
  assigns \nothing ;
  @*/
//double sqs(double x,double y) { return x*x + y*y; }

module SQS-RULE
  rule <threads>
           <thread>...
	     <k> return (x*x + y * y => V:Float); </k>
	     <env> x |-> Lx:Int y |-> Ly:Int </env>
	   ...</thread>
       </threads>
       <store> Lx |-> Vx:Float Ly |-> Vy:Float </store>
    requires DISTANCE(Vx) andBool DISTANCE(Vy)
     ensures absFloat(V -Float sqR(Vx, Vy)) <=Float E_sqs
endmodule
