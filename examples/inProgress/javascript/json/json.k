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
	
endkm

kmod JSON-PROGRAMS 
	is including JSON-SYNTAX
	
	syntax Id   ::= a | b | c | d | e | f | g | h | i | j | k | l | m
	              | n | o | p | q | r | s | t | u | v | w | x | y | z
	
	syntax JsonValue  ::= v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7
	
	macro v0 = { }
	
	macro v1 = {"s" : 234}
	
	macro v2 = {"s" : 234, "t" : "d"}
	
	macro v3 = [23, 45, 56]
	
	macro v4 = [{}, {"a" : "x", "b" : 234, "c" : true, "d" : false, "e" : [1,2,3], "f" : {"r" : 3}}]
	
	
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

