// Copyright (c) 2012-2014 K Team. All Rights Reserved.

module ISSUE

  configuration <one> .Set </one>
             <two> .Set </two>

  rule <one>... SetItem(K) => . ...</one>
       <two>  S:Set </two>
       when K in S
endmodule
