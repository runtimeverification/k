kmod STRICT-JAVASCRIPT-PROGRAMS is 
	including STRICT-JAVASCRIPT-SYNTAX

	syntax Id ::= a | b | c | f | i | j | k | m | n | q | s | t | x | y | z 
			| odd | even | odd-calls | even-calls | goto | exit
			
	syntax Exp ::= p1 | p2
	syntax Stmt ::= p3 | p4

	macro p1 = 3+5

	macro p2 = (3<=5) && !(5<=1)
	
	

endkm