module XY_SPEC
imports XY

rule
<T>
<L1>
  <k> runX </k>
</L1>
<L2>
  <k> runY </k>
</L2>
</T>

/*
rule
<T>
<L1>
  <k> 2 </k>
</L1>
<L2>
  <k> 2 </k>
</L2>
</T>
 [trusted]
*/

rule
<T>
<L1>
  <k> ?IX:Int </k>
</L1>
<L2>
  <k> ?IY:Int </k>
</L2>
</T>
requires ?IX ==K ?IY
 [trusted]



/*
rule
<T>
<L1>
  <k> runX => 2 ... </k>
</L1>
<L2>
  <k> runY => 2 ... </k>
</L2>
</T>

rule
<T>
<L1>
  <k> runX => ?IX:Int ... </k>
</L1>
<L2>
  <k> runY => ?IY:Int ... </k>
</L2>
</T>
ensures ?IX ==K ?IY
*/

endmodule
