// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
	syntax Exp ::= Exp "+" Exp

	context HOLE + _
	
	context _ + HOLE requires true
endmodule
