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

--- NEED TO REVIEW THE DATA CACHE RULES 

--- data cache with write-back policy (fully associative)
--- hit
--- NEED THESE RULES TO MAKE DATA CACHE SYMBOLIC ?
rule <k> getd(AddrS:Val32) => syint32 <_/k> if isSymbolic(AddrS)
rule <k> putd(AddrS:Val32, DataS:Val32) => . <_/k> 
		if isSymbolic(AddrS) orBool isSymbolic(DataS)

rule <k> getd(AddrS:Val32) => DataS <_/k>
     <dc_>AddrS |-> dwrap(AddrS,DataS:Val32)<_/dc>
     <dhit>H:Int32 => H +Int32 1</dhit> if notBool isSymbolic(AddrS)

--- miss (on load)
--- check again this rule and the next one
rule <k> getd(AddrS:Val32) => dmiss(AddrS) <_/k>
     <dc>DCache:Map</dc>
     if $hasMapping(DCache, AddrS) andBool 
        notBool isSymbolic(AddrS)

rule <k> getd(AddrS:Val32) => dmiss(AddrS) <_/k>
     <dc>DCache:Map</dc>
     if notBool ($hasMapping(DCache, AddrS)) andBool 
        notBool isSymbolic(AddrS)

rule <k> dmissSolved(AddrS:Val32, DataS:Val32) => DataS <_/k>
     <dc>DCache:Map (.Map => AddrS |-> dwrap(AddrS, DataS))</dc>
     <dmiss>M1:Int32 => M1 +Int32 1</dmiss>
     <t>T:Int32 => T +Int32 misstime</t>
     if notBool ($hasMapping(DCache, AddrS))

rule <k> dmissSolved(AddrS:Val32, DataS:Val32) => DataS <_/k>
     <dc>DCache:Map => DCache[dwrap(AddrS, DataS)/AddrS]</dc>
     <dmiss>M1:Int32 => M1 +Int32 1</dmiss>
     <t>T:Int32 => T +Int32 misstime</t>
     if $hasMapping(DCache, AddrS)


--- write
rule <k> putd(AddrS:Val32, DataS:Val32) => . <_/k>
     <dc_> AddrS |-> dwrap(AddrS, DataS)<_/dc> 

rule <k> putd(AddrS:Val32, DataS:Val32) => . <_/k>
     <dc>DCache:Map (.Map => AddrS |-> dwrap(AddrS, DataS))</dc>
     if notBool ($hasMapping(DCache, AddrS)) andBool 
		(currDCacheOccup(DCache) <Int32 dcachesize)

--- check again this rule and the next ones
rule <k> putd(AddrS:Val32, DataS:Val32) => . <_/k>
     <dc>DCache:Map => DCache[dwrap(AddrS, DataS)/AddrS]</dc>
     if ($hasMapping(DCache, AddrS)) andBool 
		(currDCacheOccup(DCache) <Int32 dcachesize)

--- write back 
rule <k> putd(AddrS:Val32, DataS:Val32) => write(Addr1S, Data1S) <_/k>
     <dc>DCache:Map (Addr1S:Val32 |-> 
                     (dwrap(Addr1S, Data1S:Val32) => dwrap(AddrS, DataS)))</dc>
     if (Addr1S %Int32 dcachesize) ==SyInt32 (AddrS %Int32 dcachesize)
         andBool (currDCacheOccup(DCache) <Int32 dcachesize) 

--- write back (redo)
rule <k> putd(Addr:Int32, Data:Int32) => write(Addr1, Data1) <_/k>
     <dc>DCache:Map (Addr1:Int32 |-> 
                     (dwrap(Addr1, Data1:Int32) => dwrap(Addr, Data)))</dc>
     if (Addr1 %Int32 dcachesize) ==SyInt32 (Addr %Int32 dcachesize)
         andBool (currDCacheOccup(DCache) ==SyInt32 dcachesize) 

--- end data cache with write-back policy (fully associative)


endkm
