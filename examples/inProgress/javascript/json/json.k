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
	
	syntax JsonName ::= String | Id | Int

	syntax JsonObject ::= { } | { List{JS} }
	
	syntax JsonArray ::= [ List{JS} ]
	
	syntax JsonTerminal ::= null | Bool | Numeric | JsonName
	
	syntax JsonLiteral ::= JsonTerminal | JsonObject | JsonArray
				
	syntax JsonPair ::= JsonName : JS [prec 25]
	
	syntax JS ::= JsonLiteral | JsonPair
	
endkm

kmod JSON-SEMANTICS 
	is including JSON-SYNTAX + K
	
	syntax Builtin ::= String | Bool

	syntax KResult ::= Bool | String | Numeric
	syntax K ::= JS | List{JS}
	
	
	syntax JS ::= 
			o( JSProperties ) | a( List{JS} )
		| 	buildLitObject( List{JS} , JS )
		|	buildLitArray( List{JS} , JS )
		|	buildLitTerminal( JS )
		|	b( Bool ) | n( Numeric ) | s( String )
	

	syntax JSProperty ::= p( String , JS )
	
	syntax JSProperties ::= 
			.JSProperties | JSProperty
		|	JSProperties JSProperties [assoc comm id: .JSProperties]
	
	
	macro { } = o(.JSProperties)
	
	
	
	macro { Elements:List{JS} } = buildLitObject( Elements , o(.JSProperties) )
		
	macro buildLitObject((.List{JS}) , Obj:JS ) = Obj
	
	macro buildLitObject( (Name:JsonName : Value:JS , Elements) , o(Properties:JSProperties) ) 
		= buildLitObject( (Elements) , o( p(Name, (Properties buildLitTerminal(Value))) ) )
	
	macro buildLitTerminal(null) = null
	macro buildLitTerminal(B:Bool) = b(B)
	macro buildLitTerminal(N:Numeric) = n(N)
	macro buildLitTerminal(S:String) = s(S)
	macro buildLitTerminal(o(Properties)) = o(Properties)
	macro buildLitTerminal([Elements]) = buildLitArray(Elements, a(.List{JS}))
	
	macro buildLitArray( (.List{JS}) , a(Elements) ) = a(Elements)
	
	macro buildLitArray( (Element:JS , Remaining:List{JS}) , a(Elements) ) 
		= buildLitArray( (Remaining) , a(Elements , buildLitTerminal(Element)) )

endkm

kmod JSON-PROGRAMS 
	is including JSON-SEMANTICS
	
	syntax JS  ::= v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7
	
	macro v0 = { }
	
	macro v1 = {"s" : 234}
	
	macro v2 = {"s" : 234, "t" : "d"}
	
	macro v3 = [23, 45, 56]
	
	macro v4 = [{}, {"a" : "x", "b" : 234, "c" : true, "d" : false, "e" : [1,2,3], "f" : {"r" : 3}}]	

endkm


kmod JSON is including JSON-PROGRAMS + JSON-SEMANTICS
  --- syntax Bag ::= [[ KLabel ]] | pgm
  --- macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  --- macro pgm = [['sumPgm]]
endkm

