// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module REGRESSION-MAUDE

configuration <T><k> $PGM:K </k><j> .Bag </j><one> .Set </one> <two> .Set </two></T>

rule <k> I:Int ...</k><j> .Bag => BagItem(5) </j>

rule <one>... SetItem(K) => . ...</one>
     <two>  S:Set </two>
     when K in S

syntax A ::= "a"
syntax B ::= "a"
endmodule
