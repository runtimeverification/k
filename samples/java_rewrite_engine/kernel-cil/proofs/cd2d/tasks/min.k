// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*@ ensures \result == dmin(a,b); */
/*
double mmin(double a, double b){
    return (a<=b)?a:b;
}
*/
module MIN-RULE
  rule <threads>
           <thread>...
         <k> min(Vx:Float, Vy:Float) => V:Float </k>
             <env> GENV </env>
       ...</thread>
       </threads>
       <store>... STORE ...</store>
       <genv> GENV </genv>
     ensures V ==Float dmin(Vx,Vy)
endmodule
