// Copyright (c) 2014 K Team. All Rights Reserved.

module EMPTY 
	syntax Exp ::= Exp "+" Exp

	context HOLE + _
	
	context _ + HOLE requires true
endmodule
