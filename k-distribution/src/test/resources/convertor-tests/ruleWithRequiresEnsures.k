// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
	rule A:Bool => A requires A ==K A
	rule A:Bool => A ensures A ==K A
	rule A:Bool => A requires A==K A ensures A ==K A
endmodule
