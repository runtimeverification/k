
kmod COMMON is
	including K 
	including K-CONTEXTS 
	including K-PROPER
endkm

kmod ISSUE is
	including COMMON
	
	syntax K ::= a | b | c | d | f
	
	rule a => f
	
	rule Var:K => f
		if Var:K ==Bool b
		
	--- this one actually creates an infinite loop in maude.
	rule Var:K => f
		where Var = c
	
	--- this one actually creates an infinite loop in kompile.pl.
	rule Var:K => f
		where Var:K = d
		
endkm
