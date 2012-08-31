
module ISSUE

  configuration <one> .Set </one>
	         <two> .Set </two>

  syntax K ::= K       "in" Set
             | SetItem "in" Set
				
  rule <one>... SetItem(K) => . ...</one>
        <two>  S:Set </two>
     when K in S
endmodule
