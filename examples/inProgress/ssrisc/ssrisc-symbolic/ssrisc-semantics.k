kmod SSRISC-CONFIGURATION is including SSRISC-TIME-MODEL + SSRISC-COMMUNICATION-INTERFACE + SSRISC-SYNTAX + PL-CONVERSION + K

syntax K ::= Instr | Reg | FReg 

syntax KResult ::= Val32 | Float 

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

rule <k> incPC(PC) => . <_/k>
     <pc>PC:Int32 => PC +Int32 4</pc>  

rule <k> setPC(1, NewV:Int32) => . <_/k>
     <pc>Pc:Int32 => NewV</pc> 

rule <k> setPC(0, _) => . <_/k>

--- symbolic read
rule  <k> R:Reg => Value:Val32 <_/k>
      <regs_>R |-> Value:Val32<_/regs>

--- symbolic write
rule <k> update(Value:Val32, Rd:Reg) => . </k>
     <regs_> Rd |-> (_ => Value) <_/regs>


---
--- one rule per instruction policy
---
 
--- add rd, rs, rt
rule <k> add Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 +Int32 Val2, Rd) </k>

--- addu rd, rs, rt
rule <k> addu Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 +Int32 Val2, Rd) </k>

--- addi rd, rs, imm
rule <k> addi Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 +Int32 Val2, Rd) </k>

--- addiu rd, rs, imm
rule <k> addiu Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 +Int32 Val2, Rd) </k>

--- sub rd, rs, rt
rule <k> sub Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 -Int32 Val2, Rd) </k>

--- subi rd, rs, imm
rule <k> subi Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 -Int32 Val2, Rd) </k>

--- and rd, rs, rt
rule <k> and Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 &Int32 Val2, Rd) </k>

--- andi rd, rs, imm
rule <k> andi Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 &Int32 Val2, Rd) </k>

--- or rd, rs, rt
rule <k> or Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 |Int32 Val2, Rd) </k>

--- ori rd, rs, imm
rule <k> ori Rd:Reg,Val1:Val32,Val2:Val32; => update(Val1 |Int32 Val2, Rd) </k>

--- sll rd, rs, amt
rule <k> sll Rd:Reg,Val1:Val32,V3:Nat; => update(Val1 <<Int32 V3, Rd) </k>

--- srl rd, rs, amt
rule <k> srl Rd:Reg,Val1:Val32,V3:Nat; => update(Val1 >>Int32 V3, Rd) </k>

--- to be reimplemented
--- sra rd, rs, amt
rule <k> sra Rd:Reg,Val1:Val32,V3:Nat; => update(Val1 >>Int32 V3, Rd) </k>

--- slt rd, rs, rt
rule <k> slt Rd:Reg,Val1:Val32,Val2:Val32; => update(Bool2IntSy(Val1 <SyInt32 Val2), Rd) </k>

--- slti rd, rs, imm
rule <k> slti Rd:Reg,Val1:Val32,Val2:Val32; => update(Bool2IntSy(Val1 <SyInt32 Val2), Rd) </k>

--- sltu rd, rs, rt
rule <k> sltu Rd:Reg,Val1:Val32,Val2:Val32; => update(Bool2IntSy(Val1 <SyInt32 Val2), Rd) </k>

--- sltiu rd, rs, imm
rule <k> sltiu Rd:Reg,Val1:Val32,Val2:Val32; => update(Bool2IntSy(Val1 <SyInt32 Val2), Rd) </k>

--- j addr
rule <k> j Addr:Int32; => setPC(1, Addr) </k>

--- jr reg
rule <k> jr Rs:Reg; => setPC(1, Rs) </k>

rule <k> beq Val1:Val32, Val2:Val32, Addr; => setPC(Bool2IntSy(Val1 ==BoolSy Val2), Addr) </k>

--- bne rs, rt, addr
rule <k> bne Val1:Val32, Val2:Val32, Addr; => setPC(Bool2IntSy(Val1 =/=BoolSy Val2), Addr) </k>

--- bltz rs, addr
rule <k> bltz Val1:Val32, Addr; => setPC(Bool2IntSy(Val1 <SyInt32 0), Addr) </k>

--- bgtz rs, addr
rule <k> bgtz Val1:Val32, Addr; => setPC(Bool2IntSy(Val1 >SyInt32 0), Addr) </k>

--- blez rs, addr
rule <k> blez Val1:Val32, Addr; => setPC(Bool2IntSy(Val1 <=SyInt32 0), Addr) </k>

--- bgez rs, addr
rule <k> bgez Val1:Val32, Addr; => setPC(Bool2IntSy(Val1 >=SyInt32 0), Addr) </k>

--- lui rt, imm
rule <k> lui Rt:Reg, Imm:Int32; => update(Imm, Rt) </k>

--- lw rd, off(rs)
rule <k> lw Rd:Reg, Off:Int32(Val1:Val32); => update(getd(Val1 +Int32 Off), Rd) </k>


--- lw rd, (rs+rt)
rule <k> lw Rd:Reg, (Val1:Val32 + Val2:Val32); => update(getd(Val1 +Int32 Val2), Rd) </k>

--- sw rd, off(rs)
rule <k> sw Rd:Reg, Off:Int32(Val1:Val32); => putd(Val1 +Int32 Off, Rd) </k>

--- sw rd, (rs+rt)
rule <k> sw Rd:Reg, (Val1:Val32 + Val2:Val32); => putd(Val1 +Int32 Val2, Rd) </k>
     
--- nop
rule <k> nop; => .</k>

endkm


