module EMPTY
  Bubble(rule,A:Bool => A requires A==K A ensures A ==K A,[])
  Bubble(rule,A:Bool => A requires A ==K A,[])
  Bubble(rule,A:Bool => A ensures A ==K A,[])
endmodule
