load ../../../k-prelude
kmod BASIC-ASM-SYNTAX is including PL-INT
  syntax Label ::= start
  syntax Reg ::= ax | bx | cx
  syntax UInstr ::= set Reg Int
                  | mov Reg Reg
                  | push Reg [strict]
                  | pop Reg
                  | add Reg Reg Reg [strict (1 2)]
                  | inc Reg
                  | jmp Label 
                  | nop 
                  | cmp Reg Reg [strict]
                  | jle Label
  syntax LInstr ::= Label : UInstr
  syntax Instr ::= UInstr | LInstr

  syntax Block ::= Instr | Block ; Block [gather (e E) prec 100]
endkm

kmod BASIC-ASM-PROGRAMS is  including BASIC-ASM-SYNTAX
  syntax Label ::= done | loop
  syntax Block ::= sum  
  macro sum = 
    set ax 11 ;
    set bx 0 ;
    set cx 0 ;
    loop : cmp ax bx ;
    jle done ;
    add cx bx cx ;
    inc bx ;
    jmp loop ;
    done : nop
endkm

kmod BASIC-ASM-SEMANTICS is    including BASIC-ASM-SYNTAX + K

  syntax K ::= Label | Reg | Block
  syntax KResult ::= Int 
  configuration <T> <k*> .K </k*> <nextLabel> start </nextLabel>  <cnd> 0 </cnd>
                <blocks> start |-> .K </blocks> <nextBlock> .Map </nextBlock>
                <load*> .K </load*> <regs> .Map </regs> </T>

  rule [load] : <k> .K => B </k> 
                 <nextLabel> L:Label => L' </nextLabel> 
                 <nextBlock_> L |-> L':Label <_/nextBlock>
                 <blocks_> L |-> B:Block <_/blocks> [structural]
                 
  rule [jmp] : <k> jmp L ~> _ => .K </k> <nextLabel> _ => L </nextLabel>

  rule [set] : <k> set R:Reg I:Int => . <_/k> <regs> Regs:Map => Regs[I / R] </regs>
  rule [get] : <k> R => I <_/k> <regs_> R |-> I <_/regs>
  rule [add] : <k> add I1:Int I2:Int R => . <_/k> <regs> Regs => Regs[I1 +Int I2 / R] </regs>
  rule [cmp] : <k> cmp I1 I2 => . <_/k>  <cnd> _ => I1 -Int I2 </cnd>
  rule [nop] : <k> nop => . <_/k>
  rule [jleTrue] : <k> jle L ~> _ => . </k> <nextLabel> _ => L </nextLabel> <cnd> I </cnd> if I <=Int 0
  rule [jleFalse] : <k> jle L => . </k> <cnd> I </cnd> if I >Int 0
endkm

kmod BASIC-ASM-INTERFACE is
  including BASIC-ASM-SEMANTICS
  syntax Bag ::= run ( Block ) 

  macro run( start : U:UInstr ; P:Block ) = run( U:UInstr ; P:Block ) 
  macro run( U:UInstr ; P:Block ) = <T_> <load> U:UInstr ; P:Block </load> <_/T>

  rule P1:Block ; P2:Block => P1 ~> P2 [structural]
  rule <load> U => .K <_/load> <nextLabel> L:Label </nextLabel> <blocks_> L |-> _ ~> (. => U) <_/blocks>
  rule <load> L : U => U <_/load> <nextLabel> L':Label => L </nextLabel> <blocks_> . => L |-> . <_/blocks>
       <nextBlock_> . => L' |-> L <_/nextBlock>
  rule (<load> .K </load> => <k> .K </k>) <nextLabel> _ => start </nextLabel>
endkm

kmod BASIC-ASM-TEST is
  including BASIC-ASM-INTERFACE
  including BASIC-ASM-PROGRAMS

endkm
