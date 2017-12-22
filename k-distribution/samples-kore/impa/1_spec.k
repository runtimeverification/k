module SPEC
import IMP

rule <T>
  <k> store(Loc:Int, Key:Int, Val:Int) => .K ... </k>
  <store> Loc |-> array(M1:Map => ?M2:Map) ... </store>
</T>
  requires M1[Key] ==K Val
  ensures M1 ==K ?M2
endmodule
