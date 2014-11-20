// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  Bubble(rule,A:Bool => A requires A==K A ensures A ==K A,[])
  Bubble(rule,A:Bool => A requires A ==K A,[])
  Bubble(rule,A:Bool => A ensures A ==K A,[])
endmodule
