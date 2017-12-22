module SPEC
import IMP

rule <T>
  <k> store(Loc:Int, Key:Int, Val:Int) ~>
      store(Loc2:Int, Key:Int, Val:Int) => .K ... </k>
  <store> Loc |-> array(M11:Map => ?M12:Map)
          Loc2 |-> array(M21:Map => ?M22:Map) ... </store>
</T>
  requires M11 ==K M21
  ensures ?M12 ==K ?M22
endmodule
