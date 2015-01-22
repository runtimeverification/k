// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module DNF
  // implication
  rule B1:Bool impliesBool B2:Bool => notBool(B1) orBool B2 [simplification]

  // de morgan
  rule B1:Bool andBool B2:Bool => notBool((notBool B1) andBool (notBool B2)) [simplification]

  // distributivity
  rule (B1:Bool orBool B2:Bool) andBool B3:Bool => (B1 orBool B3) andBool (B3 orBool B2) [simplification]
  rule B3:Bool andBool (B1:Bool orBool B2:Bool) => (B1 orBool B3) andBool (B3 orBool B2) [simplification]

  // negation
  rule notBool(notBool(B:Bool)) => B [simplification]
endmodule

module SIMPLIFICATION
  imports DNF
endmodule