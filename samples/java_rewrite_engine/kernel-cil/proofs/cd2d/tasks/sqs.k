// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*@
  requires DISTANCE(x) && DISTANCE(y) ;
  ensures \abs(\result - sqR(x,y)) < E_sqs ;
  assigns \nothing ;
  @*/
//double sqs(double x,double y) { return x*x + y*y; }

module SQS-RULE
  rule <threads>
           <thread>...
         <k> sqs(X:Float, Y:Float) => V:Float </k>
             <env> GENV </env>
       ...</thread>
       </threads>
       <store>... STORE ...</store>
       <genv> GENV </genv>
    requires DISTANCE(X) andBool DISTANCE(Y)
     ensures absFloat(V -Float sqR(X, Y)) <=Float E_sqs
endmodule
