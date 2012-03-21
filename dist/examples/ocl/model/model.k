require "../../k-prelude.k"

module MODEL-SYNTAX
	including K
	
	syntax Model ::= "model" #Id ":" #Id "{" Objects "}"
	syntax Objects ::= List{Object, ";"}
	
	syntax Object ::= "object" #Id ":" #Id "{" Attributes "}"
	
	syntax Attributes ::= Attribute ";"
						| Attributes 	Attributes [left]
	
	syntax Attribute ::= #Id ":" #Id "=" Data
	syntax Datas ::= List{Data,","}
	syntax Data ::= #String | #Id | #Bool | #Int | "{" Datas "}"
	
	syntax Start ::= Model
endmodule

module MODEL
	including MODEL-SYNTAX
	
	configuration 
		<T> 
			<k> $PGM:K </k>
			<model> .Bag </model>
		</T>		

endmodule