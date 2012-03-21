require "../built-ins.k"

interface #MAGMA-SYNTAX
	including PL-BUILTINS + #STRING + #FLOAT

	syntax #Object ::= #Id "::" #Id [left]
	syntax #Id ::= "string" | "real" | "int" | "bool"

	syntax #Magma ::= ".Magma"
					| #MagmaElement
					| #Magma ";Magma" #Magma [left]
					| "union" "(" #Magma "," #Magma ")"
					| "intersection" "(" #Magma "," #Magma ")"
					| "subtract" "(" #Magma "," #Magma ")"
					| "asSet" "(" #Magma ")"

	syntax #Bool ::=  "contains" "(" #MagmaElement "," #Magma ")"
					| "subset" "(" #Magma "," #Magma ")"
					| "empty" "(" #Magma ")"
					| "excludes" "(" #MagmaElement ";" #Magma ")" 
	
	syntax #Int ::= "card" "(" #Magma ")"
					| "countOcc" "(" #MagmaElement ";" #Magma ")"

	syntax #MagmaElement ::= #Int | #Bool | #String | #Float | #Object

endinterface