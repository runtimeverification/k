
module ISSUE

  configuration <one> .Set </one>
	         <two> .Set </two>

  rule <one>... SetItem(K) => . ...</one>
       <two>  S:Set </two>
       when K in S
endmodule
