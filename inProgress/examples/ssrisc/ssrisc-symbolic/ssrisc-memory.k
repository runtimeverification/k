kmod SSRISC-MEMORY is including SSRISC-COMMUNICATION-INTERFACE + SSRISC-SYNTAX + K

--- just a hack
syntax K ::= last

configuration
  <k>.K</k>
  <cmem>.Map</cmem>
  <dmem>.Map</dmem>

rule <k> imiss (PC) => imissSolved(PC, Ins) </k>
     <cmem_> PC:Int32 |-> Ins:Instr<_/cmem>

rule <k> imiss (PC) => last </k>
     <cmem>CMem:Map</cmem>
     if notBool ($hasMapping(CMem, PC))

rule <k> dmiss (AddrS) => dmissSolved(AddrS, DataS) <_/k>
     <dmem> AddrS:Val32 |-> DataS:Val32</dmem>

rule <k> dmiss (AddrS) => dmissSolved(AddrS, 0) <_/k>
     <dmem>DMem:Map (.Map => AddrS:Val32 |-> 0)</dmem>
     if notBool ($hasMapping(DMem, AddrS))

rule <k> write (Addr:Int32, Data:Int32) => . <_/k>
     <dmem_> Addr |-> (_ => Data) <_/dmem>

rule <k> write (Addr:Int32, Data:Int32) => . <_/k>
     <dmem>DMem:Map (.Map => Addr |-> Data)</dmem>
     if notBool ($hasMapping(DMem, Addr))

endkm
