require "kernelc.k"

module TEST 
  imports KERNELC

rule
  <configs>
    <config>...
      <config-id> 0 </config-id>
      <k> X:Int + Y:Int => ?K:K </k>
    ...</config>
    <config>...
      <config-id> 1 </config-id>
      <k> Y:Int + X:Int => ?K:K </k>
    ...</config>
  </configs>
  [trusted]

rule
  <configs> <config>...
    <env> X:Id |-> tv(int *, object(P:Int)) </env>
    <heap> object(P:Int) |-> tv(int, (I:Int => I:Int -Int 1)) </heap>
    <k>
      while (X != 0) { X = X - 1; S:Statement }
    =>
      S ~> while (X != 0) { X = X - 1; S:Statement } .Statements </k>
  ...</config> </configs>
  requires I >Int 0

/*
rule
  <configs>
    <config>...
      <config-id> 0 </config-id>
      <env> X:Id |-> L:Pointer </env>
      <heap> L |-> (I1:Int => ?I2:Int) </heap>
      <k> while (X != 0) { X = X - 1; S:Statement } => ?K:K </k>
    ...</config>
    <config>...
      <config-id> 1 </config-id>
      <env> X:Id |-> L:Pointer </env>
      <heap> L |-> (I1:Int => ?I2:Int) </heap>
      <k> S while (X != 0) { X = X - 1; S:Statement } => ?K:K </k>
    ...</config>
  </configs>
  requires I1 >Int 0
*/
endmodule
