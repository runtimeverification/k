kmod SSRISC-CONFIGURATION is including SSRISC-TIME-MODEL + SSRISC-COMMUNICATION-INTERFACE + SSRISC-SYNTAX + PL-CONVERSION + K

syntax K ::= Instr | Reg | FReg 

syntax KResult ::= Int32 | Float 

configuration 

    <k>.K</k>
    <pc>0</pc>
    <regs>.Map</regs>
    <fregs>.Map</fregs>

endkm
 
kmod SSRISC-SEMANTICS is including SSRISC-CONFIGURATION

--- misc rules 
rule <k> . => geti(PC) </k>
     <pc>PC:Int32</pc>  

rule  <k> R:Reg => I <_/k>
      <regs_>R |-> I:Int32<_/regs>

rule <k> incPC(PC) => . <_/k>
     <pc>PC:Int32 => PC +Int32 4</pc>  

rule <k> setPC(1, NewV:Int32) => . <_/k>
     <pc>Pc:Int32 => NewV</pc> 

rule <k> setPC(0, _) => . <_/k>

rule <k> update(I:Int32, Rd:Reg) => . </k>
     <regs_> Rd |-> (_ => I) <_/regs>

rule  <k> FR:FReg => F <_/k>
      <fregs_>FR |-> F:Float<_/fregs>

rule <k> update(F:Float, FRd:FReg) => . </k>
     <fregs_> FRd |-> (_ => F) <_/fregs>


---rule <k> ddone(Addr:Int32, Data:Int32)  => . </k>

---
--- one rule per instruction policy
---
 
--- add rd, rs, rt
rule <k> add Rd:Reg,V1:Int32,V2:Int32; => update(V1 +Int32 V2, Rd) </k>

--- addu rd, rs, rt
rule <k> addu Rd:Reg,V1:Int32,V2:Int32; => update(V1 +Int32 V2, Rd) </k>

--- addi rd, rs, imm
rule <k> addi Rd:Reg,V1:Int32,V2:Int32; => update(V1 +Int32 V2, Rd) </k>

--- addiu rd, rs, imm
rule <k> addiu Rd:Reg,V1:Int32,V2:Int32; => update(V1 +Int32 V2, Rd) </k>

--- sub rd, rs, rt
rule <k> sub Rd:Reg,V1:Int32,V2:Int32; => update(V1 -Int32 V2, Rd) </k>

--- subi rd, rs, imm
rule <k> subi Rd:Reg,V1:Int32,V2:Int32; => update(V1 -Int32 V2, Rd) </k>

--- and rd, rs, rt
rule <k> and Rd:Reg,V1:Int32,V2:Int32; => update(V1 &Int32 V2, Rd) </k>

--- andi rd, rs, imm
rule <k> andi Rd:Reg,V1:Int32,V2:Int32; => update(V1 &Int32 V2, Rd) </k>

--- or rd, rs, rt
rule <k> or Rd:Reg,V1:Int32,V2:Int32; => update(V1 |Int32 V2, Rd) </k>

--- ori rd, rs, imm
rule <k> ori Rd:Reg,V1:Int32,V2:Int32; => update(V1 |Int32 V2, Rd) </k>

--- sll rd, rs, amt
rule <k> sll Rd:Reg,V1:Int32,V3:Nat; => update(V1 <<Int32 V3, Rd) </k>

--- srl rd, rs, amt
rule <k> srl Rd:Reg,V1:Int32,V3:Nat; => update(V1 >>Int32 V3, Rd) </k>

--- to be reimplemented
--- sra rd, rs, amt
rule <k> sra Rd:Reg,V1:Int32,V3:Nat; => update(V1 >>Int32 V3, Rd) </k>

--- slt rd, rs, rt
rule <k> slt Rd:Reg,V1:Int32,V2:Int32; => update(Bool2Int(V1 <Int32 V2), Rd) </k>

--- slti rd, rs, imm
rule <k> slti Rd:Reg,V1:Int32,V2:Int32; => update(Bool2Int(V1 <Int32 V2), Rd) </k>

--- sltu rd, rs, rt
rule <k> sltu Rd:Reg,V1:Int32,V2:Int32; => update(Bool2Int(V1 <Int32 V2), Rd) </k>

--- sltiu rd, rs, imm
rule <k> sltiu Rd:Reg,V1:Int32,V2:Int32; => update(Bool2Int(V1 <Int32 V2), Rd) </k>

--- j addr
rule <k> j Addr:Int32; => setPC(1, Addr) </k>

--- jr reg
rule <k> jr Rs:Reg; => setPC(1, Rs) </k>

--- jal Imm 
rule <k> jal Imm:Int32; => setPC(1, Imm) </k>

--- beq rs, rt, addr
rule <k> beq V1:Int32, V2:Int32, Addr; => setPC(Bool2Int(V1 ==Bool V2), Addr) </k>

--- bne rs, rt, addr
rule <k> bne V1:Int32, V2:Int32, Addr; => setPC(Bool2Int(V1 =/=Bool V2), Addr) </k>

--- bltz rs, addr
rule <k> bltz V1:Int32, Addr; => setPC(Bool2Int(V1 <Int32 0), Addr) </k>

--- bgtz rs, addr
rule <k> bgtz V1:Int32, Addr; => setPC(Bool2Int(V1 >Int32 0), Addr) </k>

--- blez rs, addr
rule <k> blez V1:Int32, Addr; => setPC(Bool2Int(V1 <=Int32 0), Addr) </k>

--- bgez rs, addr
rule <k> bgez V1:Int32, Addr; => setPC(Bool2Int(V1 >=Int32 0), Addr) </k>

--- lui rt, imm
rule <k> lui Rt:Reg, Imm:Int32; => update(Imm, Rt) </k>

--- lw rd, off(rs)
rule <k> lw Rd:Reg, Off:Int32(V1:Int32); => update(getd(V1 +Int32 Off), Rd) </k>

--- lw rd, (rs+rt)
rule <k> lw Rd:Reg, (V1:Int32 + V2:Int32); => update(getd(V1 +Int32 V2), Rd) </k>

--- sw rd, off(rs)
rule <k> sw Rd:Reg, Off:Int32(V1:Int32); => putd(V1 +Int32 Off, Rd) </k>

--- sw rd, (rs+rt)
rule <k> sw Rd:Reg, (V1:Int32 + V2:Int32); => putd(V1 +Int32 V2, Rd) </k>
     
--- nop
rule <k> nop; => .</k>

--- add.s rd, rs, rt
rule <k> add.s FRd:FReg,FV1:Float,FV2:Float; => update(FV1 +Float FV2, FRd) </k>

--- add.d rd, rs, rt
rule <k> add.d FRd:FReg,FV1:Float,FV2:Float; => update(FV1 +Float FV2, FRd) </k>

--- sub.s rd, rs, rt
rule <k> sub.s FRd:FReg,FV1:Float,FV2:Float; => update(FV1 -Float FV2, FRd) </k>

--- sub.d rd, rs, rt
rule <k> sub.d FRd:FReg,FV1:Float,FV2:Float; => update(FV1 -Float FV2, FRd) </k>

--- mul.s rd, rs, rt
rule <k> mul.s FRd:FReg,FV1:Float,FV2:Float; => update(FV1 *Float FV2, FRd) </k>

--- mul.d rd, rs, rt
rule <k> mul.d FRd:FReg,FV1:Float,FV2:Float; => update(FV1 *Float FV2, FRd) </k>

--- div.s rd, rs, rt
rule <k> div.s FRd:FReg,FV1:Float,FV2:Float; => update(FV1 /Float FV2, FRd) </k>

--- div.d rd, rs, rt
rule <k> div.d FRd:FReg,FV1:Float,FV2:Float; => update(FV1 /Float FV2, FRd) </k>

endkm


