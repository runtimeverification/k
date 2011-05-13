kmod SSRISC-DCACHE-SYNTAX is including K 

syntax K ::= dwrap ( K , K ) 

endkm

kmod SSRISC-DCACHE-SEMANTICS is including SSRISC-TIME-MODEL + SSRISC-COMMUNICATION-INTERFACE + SSRISC-DCACHE-SYNTAX + SSRISC-SYNTAX

configuration 
    <k>.K</k>
    <dc>.Map</dc>
    <profile>
      <dmiss>0</dmiss>
      <dhit>0</dhit>
    </profile>

syntax Int32 ::= dcachesize
macro dcachesize = 10

syntax Int32 ::= currDCacheOccup ( Map ) 
macro currDCacheOccup(M:Map (K1:K |-> K2:K)) = currDCacheOccup(M) +Int32 1 
macro currDCacheOccup(.) = 0

***(
--- data cache with write-through policy (direct mapped)
--- hit
rule <k> getd(Addr:Int32) => Data <_/k>
     <dc_>Addr1:Int32 |-> dwrap(Addr, Data:Int32)<_/dc>
     <dhit>H:Int32 => H +Int32 1</dhit>
     if (Addr1 ==Bool Addr %Int32 dcachesize) 

--- miss (on load)
rule <k> getd(Addr:Int32) => dmiss(Addr) <_/k>
     <dc_>DCid:Int32 |-> dwrap(X:Int32, Data:Int32) <_/dc>
     if (DCid ==Bool Addr %Int32 dcachesize) andBool (X =/=Bool Addr)

rule <k> dmissSolved(Addr:Int32, Data:Int32) => Data <_/k>
     <dc_>DCid:Int32 |-> (_ => dwrap(Addr, Data))<_/dc>
     <dmiss>M1:Int32 => M1 +Int32 1</dmiss>
     if (DCid ==Bool Addr %Int32 dcachesize)

--- write (on store)
rule <k> putd(Addr:Int32, Data:Int32) => write (Addr, Data) <_/k>
     <dc_>DCid:Int32 |-> (_ => dwrap(Addr,Data))<_/dc>
     if (DCid ==Bool Addr %Int32 dcachesize)

--- end data cache with write-through policy (direct mapped)
***)


--- data cache with write-back policy (fully associative)
--- hit
rule <k> getd(Addr:Int32) => Data <_/k>
     <dc_>Addr |-> dwrap(Addr,Data:Int32)<_/dc>
     <dhit>H:Int32 => H +Int32 1</dhit>

--- miss (on load)
rule <k> getd(Addr:Int32) => dmiss(Addr) <_/k>
     <dc>DCache:Map</dc>
     if notBool ($hasMapping(DCache, Addr))

rule <k> getd(Addr:Int32) => dmiss(Addr) <_/k>
     <dc_>Addr |-> dwrap(Addr1,Data:Int32)<_/dc>
     if notBool (Addr ==Int32 Addr1)

rule <k> dmissSolved(Addr:Int32, Data:Int32) => Data <_/k>
     <dc>DCache:Map (.Map => Addr |-> dwrap(Addr, Data))</dc>
     <dmiss>M1:Int32 => M1 +Int32 1</dmiss>
     <t>T:Int32 => T +Int32 misstime</t>
***(     if notBool ($hasMapping(DCache, Addr))

rule <k> dmissSolved(Addr:Int32, Data:Int32) => Data <_/k>
     <dc>DCache:Map (.Map => Addr |-> dwrap(Addr, Data))</dc>
     <dmiss>M1:Int32 => M1 +Int32 1</dmiss>
     <t>T:Int32 => T +Int32 misstime</t>
     if notBool ($hasMapping(DCache, Addr))
***)
--- write
rule <k> putd(Addr:Int32, Data:Int32) => . <_/k>
     <dc_> Addr |-> dwrap(Addr, Data)<_/dc> 

rule <k> putd(Addr:Int32, Data:Int32) => . <_/k>
     <dc>DCache:Map (.Map => Addr |-> dwrap(Addr, Data))</dc>
     if notBool ($hasMapping(DCache, Addr)) andBool 
		(currDCacheOccup(DCache) <Int32 dcachesize)

--- write back 
rule <k> putd(Addr:Int32, Data:Int32) => write(Addr1, Data1) <_/k>
     <dc>DCache:Map (Addr1:Int32 |-> 
                     (dwrap(Addr1, Data1:Int32) => dwrap(Addr, Data)))</dc>
     if (Addr1 %Int32 dcachesize) ==Int32 (Addr %Int32 dcachesize) andBool
         currDCacheOccup(DCache) <Int32 dcachesize 

--- write back (redo)
rule <k> putd(Addr:Int32, Data:Int32) => write(Addr1, Data1) <_/k>
     <dc>DCache:Map (Addr1:Int32 |-> 
                     (dwrap(Addr1, Data1:Int32) => dwrap(Addr, Data)))</dc>
     if (Addr1 %Int32 dcachesize) ==Int32 (Addr %Int32 dcachesize) andBool
         currDCacheOccup(DCache) ==Int32 dcachesize 

rule <k> putd(Addr:Int32, Data:Int32) => write(Addr1, Data1) <_/k>
     <dc>DCache:Map (Addr1:Int32 |-> 
                     (dwrap(Addr1, Data1:Int32) => dwrap(Addr, Data)))</dc>



--- end data cache with write-back policy (fully associative)


endkm
