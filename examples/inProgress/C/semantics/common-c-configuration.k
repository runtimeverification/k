kmod COMMON-C-CONFIGURATION is
	including C-SYNTAX
	including MATCH-C-SYNTAX
	
	op k : -> CellLabel
	op stackFrame : -> CellLabel
	op continuation : -> CellLabel
	
	subsort Id Int String Float Bool Rat < K
	subsort String < Builtins
	
	subsort C < K
	subsort List{C} < K
endkm
