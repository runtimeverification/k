// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module EXISTSLHSBOUNDFAIL-SYNTAX
  imports INT-SYNTAX
endmodule

module EXISTSLHSBOUNDFAIL
  imports EXISTSLHSBOUNDFAIL-SYNTAX
  imports INT

//  rule { C #Equals { C }:>Int } => #Exists I1. { C #Equals I1:Int } [simplification]
  rule { C #Equals { C }:>Int } => #Exists ?I1. { C #Equals ?I1:Int } [simplification]
endmodule
