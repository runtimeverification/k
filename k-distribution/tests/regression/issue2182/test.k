// Copyright (c) 2015-2019 K Team. All Rights Reserved.
module TEST

configuration <T>
  <k> @InitConfig </k>
  <objs>
    <obj multiplicity="*"> .K </obj>
  </objs>
</T>

syntax KItem ::= "@InitConfig"
rule <k> @InitConfig => . ... </k>
     <objs>
       .Bag =>
            <obj> 1 </obj>
            <obj> 2 </obj>
            <obj> 3 </obj>
            <obj> 4 </obj>
            <obj> 5 </obj>
            <obj> 6 </obj>
            <obj> 7 </obj>
            <obj> 8 </obj>
            <obj> 9 </obj>
            <obj> 10 </obj>
            <obj> 11 </obj>
            <obj> 12 </obj>
            <obj> 13 </obj>
            <obj> 14 </obj>  // 2.7GB  10sec
            <obj> 15 </obj>  // 3.4GB  20sec
            <obj> 16 </obj>  // 5.6GB  60sec
            <obj> 17 </obj>  // java.lang.OutOfMemoryError

     </objs>

endmodule
