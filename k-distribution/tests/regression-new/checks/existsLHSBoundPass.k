// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module EXISTSLHSBOUNDPASS-SYNTAX
  imports INT-SYNTAX
endmodule

module EXISTSLHSBOUNDPASS
  imports EXISTSLHSBOUNDPASS-SYNTAX
  imports INT

  rule { C #Equals { C }:>Int } => #Exists I1. { C #Equals I1:Int } [simplification]
//  rule { C #Equals { C }:>Int } => #Exists ?I1. { C #Equals ?I1:Int } [simplification]
endmodule
