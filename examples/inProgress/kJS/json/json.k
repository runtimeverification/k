--- This file needs to be processed by the K-Maude tool

in ../../../../k-prelude

kmod JSON-LIST
	is including PL-INT + PL-FLOAT + PL-STRING + PL-ID
	
	syntax JS ::= null | Int | Float | Bool

	syntax List{JS} ::= JS | .List{JS} | List{JS} , List{JS} [assoc id: .List{JS}]
	
endkm

kmod JSON-SYNTAX 
	is including JSON-LIST
	
	syntax Numeric ::= Int | Float
	
	syntax JsonKey ::= String | Id | Int

	syntax JsonObject ::= { } | { List{JS} }
	
	syntax JsonArray ::= [ ] | [ List{JS} ]
	
	syntax JsonTerminal ::= null | Bool | Numeric | JsonKey
	
	syntax JsonLiteral ::= JsonTerminal | JsonObject | JsonArray
				
	syntax JsonPair ::= JsonKey : JS [prec 25]
	
	syntax JS ::= JsonLiteral | JsonPair
	
endkm

kmod JSON
	is including JSON-SYNTAX + K
	
	syntax Builtin ::= String | Bool

	syntax KResult ::= Bool | String | Numeric
	syntax K ::= JS | List{JS}
	
	syntax JS ::= 
			o( JSProperties ) | a( List{JS} )
		| 	buildLitObject( List{JS} , JS )
	

---	syntax JSProperty ::= p( JsonKey , JS )
	syntax JSProperty ::= JsonPair
	
	syntax JSProperties ::= 
			.JSProperties | JSProperty
		|	JSProperties JSProperties [assoc comm id: .JSProperties]
	

	macro [] = a(.List{JS})
	macro [ Elements ] = a( Elements )

	macro { } = o(.JSProperties)	


	macro { Elements:List{JS} } = buildLitObject( Elements , o(.JSProperties) )

	macro buildLitObject((.List{JS}) , Obj:JS ) = Obj

---	macro buildLitObject( (Key:JsonKey : Value:JS , Elements) , o(Properties:JSProperties) ) 
---		= buildLitObject( (Elements) , o(Properties p(Key, Value)) )
	macro buildLitObject( (Key:JsonKey : Value:JS , Elements) , o(Properties:JSProperties) ) 
		= buildLitObject( (Elements) , o(Properties Key : Value) )

endkm

