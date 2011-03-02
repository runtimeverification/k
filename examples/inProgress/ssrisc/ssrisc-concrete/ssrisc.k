require ../../k-prelude.maude
require ssrisc-time-model
require ssrisc-syntax
require ssrisc-semantics
require ssrisc-icache
require ssrisc-dcache
require ssrisc-memory
require ssrisc-programs

kmod SSRISC is including SSRISC-SEMANTICS + SSRISC-ICACHE-SEMANTICS + SSRISC-DCACHE-SEMANTICS + SSRISC-MEMORY + SSRISC-PROGRAMS

configuration 

    <T>
    <k>.K</k>
    <pc>0</pc>
    <regs>.Map</regs>
    <cmem>.Map</cmem>
    <dmem>.Map</dmem>
    <ic>.Map</ic>
    <dc>.Map</dc>
    <profile>
      <imiss>0</imiss>
      <ihit>0</ihit>
      <dmiss>0</dmiss>
      <dhit>0</dhit>
    </profile>
    <t>0</t>
  </T>


syntax Bag ::= run-with-ic ( Map , Map , Map , Map ) 

rule run-with-ic(P:Map,R:Map,S:Map,T1:Map) =>
        <T_> <k>.K</k>
             <pc>1016</pc>
             <regs>R</regs>
             <cmem>P</cmem>
             <ic>S</ic>
             <dc>T1</dc>
             <profile>
                <ihit>0</ihit>
                <imiss>0</imiss>
                <dmiss>0</dmiss>
                <dhit>0</dhit>
             </profile>
             <t>0</t>
        <_/T> [structural]

endkm
