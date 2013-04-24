module ISSUE
  
  syntax K ::= "read" 
 
  configuration <T>
		  <k> $PGM:K </k>
		  <in stream="stdin"> $IN:List </in>
		</T>

  rule <k> read => I ...</k>
       <in> ListItem(I) => . ...</in>

endmodule