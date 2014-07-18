// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*@
  requires DISTANCE(Sx) && DISTANCE(Sy) ;
  ensures horizontal_losR(s_x,s_y,D) ==> TRUE(\result);
  assigns \nothing ;
  @*/
/*
int horizontal_los(double s_x, double s_y)
{
  double sqS = sqs(s_x, s_y);
  double sqD = D*D;
  return (sqS - sqD <= E_hlos);
}
*/

module HORIZONTAL-LOS-RULE
  rule <threads>
           <thread>...
         <k> horizontal_los(Sx:Float, Sy:Float) => V:Bool </k>
             <env> GENV </env>
       ...</thread>
       </threads>
       <store>... STORE ...</store>
       <genv> GENV </genv>
    requires DISTANCE(Sx) andBool DISTANCE(Sy) andBool horizontalLosR(Sx,Sy,5.0)
     ensures V
endmodule
