// Copyright (c) 2015 K Team. All Rights Reserved.
// This is the substitution currently used by lambda.k
module SUBSTITUTION
  syntax K ::= K "[" K "/" K "]" [function, hook(SUBSTITUTION.userSubstitutionKore), impure]
endmodule
