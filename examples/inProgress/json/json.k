--- This file needs to be processed by the K-Maude tool
in ../../../k-prelude

kmod JSON-SYNTAX 
	is including PL-INT + PL-FLOAT + PL-STRING + PL-ID + K
	
	syntax JsonNumber ::= Int | Float 
	
	syntax JsonKey ::= String | Id | Int

	syntax JsonTerminal ::= undefined | null | Bool | JsonNumber | JsonKey

	syntax JsonObject ::= { } | { List{JsonElement} }
	
	syntax JsonArray ::= [ ] | [ List{JsonElement} ]
	
	syntax JsonLiteral ::= JsonTerminal | JsonObject | JsonArray
	
	syntax JsonProperty ::= JsonKey : JsonLiteral [prec 25]
	
	syntax JsonElement ::= JsonProperty | JsonLiteral
	
	syntax List{JsonElement} ::= 
			.List{JsonElement} | JsonElement 
		|	List{JsonElement} , List{JsonElement} [assoc id: .List{JsonElement}]
endkm

kmod JSON
	is including JSON-SYNTAX + K
	
	syntax Builtin ::= String | Bool

	syntax KResult ::= JsonTerminal
	
	syntax K ::= JsonLiteral
	
	syntax JsonLiteral ::= 
			o( JsonProperties ) | a( List{JsonElement} )
		| 	buildLitObject( List{JsonElement} , JsonProperties )

	syntax JsonProperties ::= 
			.JsonProperties | JsonProperty 
		|	JsonProperties JsonProperties [assoc comm id: .JsonProperties]

	macro [ ] = [ .List{JsonElement} ]
	macro [ Elements:List{JsonElement} ] = a( Elements )
	
	macro { } = o(.JsonProperties)
	macro { Elements } = buildLitObject( Elements , .JsonProperties )

	macro buildLitObject((.List{JsonElement}) , Properties:JsonProperties ) = o(Properties)

	macro buildLitObject( (Key:JsonKey : Value:JsonLiteral , Elements) , Properties ) 
		= buildLitObject( (Elements) , Properties Key : Value )
endkm
