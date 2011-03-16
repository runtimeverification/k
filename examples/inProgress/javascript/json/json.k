--- This file needs to be processed by the K-Maude tool

in ../../../../k-prelude

kmod JSON-SYNTAX 
	is including PL-INT + PL-FLOAT + PL-STRING + PL-ID
	
	syntax JsonName ::= String | Id
	
	syntax JsonValue ::= null | JsonObject | JsonArray | JsonName | Int | Float | Bool
	
	syntax JsonObject ::= { } | { List{JsonElem} }
	
	syntax JsonPair ::= JsonName : JsonValue 
	
	syntax JsonElem ::= JsonValue | JsonPair 
	
	syntax List{JsonElem} ::= JsonElem | .List{JsonElem}
				| List{JsonElem} , List{JsonElem} [prec 50 assoc id: .List{JsonElem}]
	
	syntax JsonArray ::= [ List{JsonElem} ]
	
	
	syntax JSProperties ::= .JSProperties | 
							jsProp( JsonName , JsonValue ) | 
							JSProperties JSProperties [prec 50 assoc comm id: .JSProperties]
	
	syntax JSObject ::= jsObj( JSProperties ) | 
						internalize ( JsonObject ) |
						buildJsObj( List{JsonElem} , JSObject )
	
	macro internalize({ Elements:List{JsonElem} }) = buildJsObj( Elements , jsObj(.JSProperties) )
		
	macro buildJsObj((.List{JsonElem}) , Obj:JSObject ) = Obj
	macro buildJsObj((Name:JsonName : Value:JsonValue , Elements) , jsObj(Properties:JSProperties) ) 
		= buildJsObj((Elements) , jsObj(jsProp(Name, Value) Properties))
	
endkm

kmod JSON-PROGRAMS 
	is including JSON-SYNTAX
	
---	syntax Id   ::= a | b | c | d | e | f | g | h | i | j | k | l | m
---	              | n | o | p | q | r | s | t | u | v | w | x | y | z
	
	syntax JsonValue  ::= v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7
	
	macro v0 = { }
	
	macro v1 = {"s" : 234}
	
	macro v2 = {"s" : 234, "t" : "d"}
	
	macro v3 = [23, 45, 56]
	
	macro v4 = [{}, {"a" : "x", "b" : 234, "c" : true, "d" : false, "e" : [1,2,3], "f" : {"r" : 3}}]
	
	syntax JSObject  ::= js0 | js1 | js2 | js3 | js4
	
	macro js0 = internalize(v0)
	
	macro js1 = internalize(v1)
	
	macro js2 = internalize(v2)
	
	macro js3 = internalize(v3)
	
	macro js4 = internalize(v4)
	

endkm

kmod JSON-SEMANTICS is including JSON-SYNTAX + K
	syntax Builtin ::= String
	
	syntax KResult ::= Bool | Int | Float | String
	syntax K ::= JsonValue | JsonArray | JsonObject | JsonName | JsonPair | JsonElem | List{JsonElem}

endkm

kmod JSON is including JSON-PROGRAMS + JSON-SEMANTICS
  --- syntax Bag ::= [[ KLabel ]] | pgm
  --- macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  --- macro pgm = [['sumPgm]]
endkm

