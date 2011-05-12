--- This file needs to be processed by the K-Maude tool



kmod JSON-LIST
	is including PL-INT + PL-FLOAT + PL-STRING + PL-ID
	
	syntax JS ::= undefined | null | Int | Float | Bool

	syntax List{JS} ::= JS | .List{JS} | List{JS} , List{JS} [assoc id: .List{JS}]
	
endkm

kmod JSON-SYNTAX 
	is including JSON-LIST
	
	syntax JsonNumeric ::= Int | Float
	
	syntax JsonKey ::= String | Id | Int

	syntax JsonObject ::= { } | { List{JS} }
	
	syntax JsonArray ::= [ ] | [ List{JS} ]
	
	syntax JsonTerminal ::= undefined | null | Bool | JsonNumeric | JsonKey
	
	syntax JsonLiteral ::= JsonTerminal | JsonObject | JsonArray
				
	syntax JsonPair ::= JsonKey : JS [prec 25]
	
	syntax JS ::= JsonLiteral | JsonPair
	
endkm

kmod JSON
	is including JSON-SYNTAX + K
	
	syntax Builtin ::= String | Bool

	syntax KResult ::= Bool | String | JsonNumeric
	syntax K ::= JS | List{JS}
	
	syntax JS ::= 
			o( JSProperties ) | a( List{JS} )
		| 	buildLitObject( List{JS} , JSProperties )
	

	syntax JSProperty ::= JsonPair
	
	syntax JSProperties ::= 
			.JSProperties | JSProperty 
		|	JSProperties JSProperties [assoc comm id: .JSProperties]
	

	macro [] = a(.List{JS})
	macro [ Elements ] = a( Elements )

	macro { } = o(.JSProperties)	


	macro { Elements:List{JS} } = buildLitObject( Elements , .JSProperties )

	macro buildLitObject((.List{JS}) , Properties:JSProperties ) = o(Properties)

	macro buildLitObject( (Key:JsonKey : Value:JS , Elements) , Properties ) 
		= buildLitObject( (Elements) , Properties Key : Value )

endkm


---	syntax JSProperty ::= p( JsonKey , JS )
---	macro buildLitObject( (Key:JsonKey : Value:JS , Elements) , o(Properties:JSProperties) ) 
---		= buildLitObject( (Elements) , o(Properties p(Key, Value)) )
