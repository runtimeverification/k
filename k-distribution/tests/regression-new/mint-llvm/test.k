// Copyright (c) K Team. All Rights Reserved.
module TEST
  imports MINT

  syntax MInt{8}
  syntax Number ::= Int | MInt{8}

  syntax AExp ::= Number
                | "~" AExp [strict]
                | "-" AExp [strict]
                > AExp "*" AExp [strict]
                | AExp "/" AExp [strict]
                | AExp "%" AExp [strict]
                > AExp "+" AExp [strict]
                | AExp "-" AExp [strict]
                > AExp ">>" AExp [strict]
                | AExp "<<" AExp [strict]
                > AExp "&" AExp [strict]
                > AExp "^" AExp [strict]
                > AExp "|" AExp [strict]

  syntax BExp ::= Bool
                | AExp "<" AExp [strict]
                | AExp "<=" AExp [strict]
                | AExp ">" AExp [strict]
                | AExp ">=" AExp [strict]
                | AExp "==" AExp [strict]
                | AExp "!=" AExp [strict]

  syntax KResult ::= MInt{8} | Bool

  rule I:Int => Int2MInt(I)::MInt{8}

  rule ~ I => ~MInt I
  rule - I => --MInt I
  rule I * J => I *MInt J
  rule I / J => I /sMInt J
  rule I % J => I %sMInt J
  rule I + J => I +MInt J
  rule I - J => I -MInt J
  rule I >> J => I >>aMInt J
  rule I << J => I <<MInt J
  rule I & J => I &MInt J
  rule I ^ J => I xorMInt J
  rule I | J => I |MInt J

  rule I < J => I <sMInt J
  rule I <= J => I <=sMInt J
  rule I > J => I >sMInt J
  rule I >= J => I >=sMInt J
  rule I == J => I ==MInt J
  rule I != J => I =/=MInt J

endmodule
