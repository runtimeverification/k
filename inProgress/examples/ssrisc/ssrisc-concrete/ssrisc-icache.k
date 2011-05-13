kmod SSRISC-ICACHE-SYNTAX is including K 

syntax K ::= iwrap ( K , K )           

endkm


kmod SSRISC-ICACHE-SEMANTICS is including SSRISC-TIME-MODEL + SSRISC-COMMUNICATION-INTERFACE + SSRISC-ICACHE-SYNTAX + SSRISC-SYNTAX

configuration  
    <k>.K</k>
    <ic>.Map</ic>
    <profile>
      <imiss>0</imiss>
      <ihit>0</ihit>
    </profile>

syntax Int32 ::= icachesize
macro icachesize = 10

syntax Int32 ::= currICacheOccup ( Map ) 
macro currICacheOccup(M:Map (K1:K |-> K2:K)) = currICacheOccup(M) +Int32 1 
macro currICacheOccup(.) = 0


--- instruction cache (direct mapped)
--- hit
rule <k> geti(PC:Int32) => incPC(PC) ~> Ins </k>
     <ic_>_ |-> iwrap(PC,Ins:Instr)<_/ic>
     <ihit>H:Int32 => H +Int32 1</ihit>
     <t>T:Int32 => T +Int32 hittime</t>

---miss
rule <k> geti(PC:Int32) => imiss(PC) </k>
     <ic_> ICpc:Int32 |-> iwrap(X:Int32,_) <_/ic>
     if (ICpc ==Bool PC %Int32 icachesize) andBool (X =/=Bool PC) 

rule <k> imissSolved(PC:Int32, Ins:Instr) => incPC(PC) ~> Ins </k>
     <ic_> ICpc:Int32 |-> ( _ => iwrap(PC,Ins)) <_/ic>
     <imiss>M1:Int32 => M1 +Int32 1</imiss>
     <t>T:Int32 => T +Int32 misstime</t>
     if (ICpc ==Bool PC %Int32 icachesize)

--- end instruction cache (direct mapped)

***(
--- instruction cache (fully associative)
--- hit
rule <k> geti(PC:Int32) => incPC(PC) ~> Ins </k>
     <ic_>_ |-> iwrap(PC,Ins:Instr)<_/ic>
     <ihit>H:Int32 => H +Int32 1</ihit>
     <t>T:Int32 => T +Int32 hittime</t>

---miss
rule <k> geti(PC:Int32) => imiss(PC) <_/k>
     <ic>ICache:Map</ic>
     if notBool ($hasMapping(ICache, PC))

rule <k> imissSolved(PC:Int32, Ins:Instr) => incPC(PC) ~> Ins </k>
     <ic>ICache:Map ( .Map => PC %Int32 icachesize |-> iwrap(PC,Ins)) </ic>
     <imiss>M1:Int32 => M1 +Int32 1</imiss>
     <t>T:Int32 => T +Int32 misstime</t>
     if notBool ($hasMapping(ICache, PC %Int32 icachesize)) andBool 
        (currICacheOccup(ICache) <Int32 icachesize) 
     
rule <k> imissSolved(PC:Int32, Ins:Instr) => incPC(PC) ~> Ins </k>
     <ic>ICache:Map (PC %Int32 icachesize |-> (_ => iwrap(PC,Ins))) </ic>
     <imiss>M1:Int32 => M1 +Int32 1</imiss>
     <t>T:Int32 => T +Int32 misstime</t>
     if (currICacheOccup(ICache) <Int32 icachesize) 
***)
endkm


