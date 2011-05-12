kmod SSRISC-TIME-MODEL is including K + PL-INT32
 
  syntax KResult ::= Val32

  syntax Int32 ::= hittime | misstime

  macro hittime = 1
  macro misstime = 5

  configuration
    <t>0</t>
    <profile>.K</profile>


  --- operators defined over symbolic values  
  syntax Val32 ::=  Val32 +Int32 Val32 [ditto strict] 
  rule syint32 +Int32 I2:Val32 => syint32 [structural]

  syntax Val32 ::= Val32 -Int32  Val32 [ditto strict] 
  rule syint32 -Int32 I2:Val32 => syint32 [structural]

  syntax Val32 ::= Val32 &Int32 Val32 [ditto strict] 
  rule syint32 &Int32 I2:Val32 => syint32 [structural]

  syntax Val32 ::=  Val32 |Int32 Val32 [ditto strict]
  rule syint32 |Int32 I2:Val32 => syint32 [structural]

  syntax Val32 ::= Val32 <<Int32 Nat [ditto strict]
  rule syint32 <<Int32 I3:Nat => syint32 [structural]

  syntax Val32 ::= Val32 >>Int32 Nat [ditto strict] 
  rule syint32 >>Int32 I3:Nat => syint32 [structural]

  syntax Val32 ::= Val32 %Int32 Val32 [ditto strict]
  rule syint32 %Int32 I2:Val32 => syint32 [structural]

  syntax Bool ::= Val32 ==SyInt32 Val32 [strict]
  rule syint32 ==SyInt32 I2:Val32 => true 
  rule syint32 ==SyInt32 I2:Val32 => false
  rule I2:Val32 ==SyInt32 syint32 => true
  rule I2:Val32 ==SyInt32 syint32 => false
  rule I1:Int32 ==SyInt32 I2:Int32 => I1:Int32 ==Int32 I2:Int32


  syntax Bool ::= Val32 <SyInt32 Val32 [strict]
  rule syint32 <SyInt32 I:Int32 => true
  rule syint32 <SyInt32 I:Int32 => false
  rule I2:Val32 <SyInt32 syint32 => true
  rule I2:Val32 <SyInt32 syint32 => false
  rule I1:Int32 <SyInt32 I2:Int32 => I1:Int32 <Int32 I2:Int32

  syntax Bool ::= Val32 >SyInt32 Val32 [strict]
  rule syint32 >SyInt32 I:Int32 => true
  rule syint32 >SyInt32 I:Int32 => false
  rule I2:Val32 >SyInt32 syint32 => true
  rule I2:Val32 >SyInt32 syint32 => false
  rule I1:Int32 >SyInt32 I2:Int32 => I1:Int32 >Int32 I2:Int32

  syntax Bool ::= Val32 >=SyInt32 Val32 [strict]
  rule syint32 >=SyInt32 I:Int32 => true
  rule syint32 >=SyInt32 I:Int32 => false
  rule I2:Val32 >=SyInt32 syint32 => true
  rule I2:Val32 >=SyInt32 syint32 => false
  rule I1:Int32 >=SyInt32 I2:Int32 => I1:Int32 >=Int32 I2:Int32

  syntax Bool ::= Val32 <=SyInt32 Val32 [strict]
  rule syint32 <=SyInt32 I:Int32 => true
  rule syint32 <=SyInt32 I:Int32 => false
  rule I2:Val32 <=SyInt32 syint32 => true
  rule I2:Val32 <=SyInt32 syint32 => false
  rule I1:Int32 <=SyInt32 I2:Int32 => I1:Int32 <=Int32 I2:Int32

  syntax Bool ::= Val32 ==BoolSy Val32 [strict]
  rule syint32 ==BoolSy I:Int32 => true 
  rule syint32 ==BoolSy I:Int32 => false 
  rule I2:Val32 ==BoolSy syint32 => true 
  rule I2:Val32 ==BoolSy syint32 => false 
  rule I1:Int32 ==BoolSy I2:Int32 => I1:Int32 ==Bool I2:Int32 

  syntax Bool ::= Val32 =/=BoolSy Val32 [strict]
  rule syint32 =/=BoolSy I:Int32 => true 
  rule syint32 =/=BoolSy I:Int32 => false 
  rule I2:Val32 =/=BoolSy syint32 => true 
  rule I2:Val32 =/=BoolSy syint32 => false 
  rule I1:Int32 =/=BoolSy I2:Int32 => I1:Int32 =/=Bool I2:Int32 

  syntax Val32 ::= Bool2IntSy( Bool ) [strict]
  rule Bool2IntSy(true) => 1 [structural]
  rule Bool2IntSy(false) => 0 [structural] 

endkm


kmod SSRISC-COMMUNICATION-INTERFACE is including K

--- geti, idone, imiss, imissSolved are used for instruction cache modeling
--- getd, dmiss, dmissSolved are used for data cache modeling (load)
--- putd, write are used for data cache modeling (store)
syntax CacheAux ::= geti ( K ) 
                  | getd ( K ) [strict]
                  | putd ( K , K )  [strict(2)]
                  | imiss ( K ) 
                  | dmiss ( K ) 
                  | imissSolved ( K , K ) 
                  | dmissSolved ( K , K ) 
                  | write ( K , K ) 

syntax K ::= CacheAux

endkm
