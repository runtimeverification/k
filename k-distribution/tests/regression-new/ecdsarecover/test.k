// Copyright (c) K Team. All Rights Reserved.
module TEST
  imports INT
  imports STRING

  syntax String ::= ECDSARecover ( String , Int , String , String ) [function, hook(KRYPTO.ecdsaRecover)]
endmodule
