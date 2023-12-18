// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module TEST
  syntax Exp

  rule A:Exp => A requires A
  rule A:Exp => A ensures A
  rule A:Exp => A requires A ensures A
endmodule
