kmod SSRISC-TIME-MODEL is including K + PL-INT32
 
  syntax KResult ::= Int32

  syntax Int32 ::= hittime | misstime

  macro hittime = 1
  macro misstime = 5

  configuration
    <t>0</t> 
    <profile>.K</profile>

endkm


kmod SSRISC-COMMUNICATION-INTERFACE is including K

--- geti, idone, imiss, imissSolved are used for instruction cache modeling
--- getd, dmiss, dmissSolved are used for data cache modeling (load)
--- putd, write are used for data cache modeling (store)
syntax CacheAux ::= geti ( K ) 
                  | getd ( K ) 
                  | putd ( K , K )  [strict(2)]
                  | imiss ( K ) 
                  | dmiss ( K ) 
                  | imissSolved ( K , K ) 
                  | dmissSolved ( K , K ) 
                  | write ( K , K ) 

syntax K ::= CacheAux

endkm
