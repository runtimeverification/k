kmod SSRISC-SYNTAX is including PL-INT32 + PL-UNSIGNED-INT32 + PL-ID + PL-FLOAT + K 

syntax Reg ::= Int32 

syntax FReg ::= Float

syntax Imm ::= Int32

syntax Amt ::= Nat

syntax Addr ::= Int32

syntax Off ::= Int32

syntax Instr ::= add Reg , Reg , Reg ; [strict (2 3)]
               | addu Reg , Reg , Reg ; [strict (2 3)]
	       | addi Reg , Reg , Imm ; [strict (2)]
               | addiu Reg , Reg , Imm ; [strict (2)]
               | sub Reg , Reg , Reg ; [strict (2 3)]
               | subi Reg , Reg , Imm ; [strict (2)]
	       | and Reg , Reg , Reg ; [strict (2 3)]
	       | andi Reg , Reg , Imm ; [strict (2)]
               | or Reg , Reg , Reg ; [strict (2 3)]
               | ori Reg , Reg , Imm ; [strict (2)]
	       | sll Reg , Reg , Amt ; [strict (2)]
               | srl Reg , Reg , Amt ; [strict (2)]
               | sra Reg , Reg , Amt ; [strict (2)]
               | slt Reg , Reg , Reg ; [strict (2 3)]
               | slti Reg , Reg , Imm ; [strict (2)]
               | sltu Reg , Reg , Reg ; [strict (2 3)]
               | sltiu Reg , Reg , Imm ; [strict (2)]
               | j Addr ; 
               | jr Reg ;
               | jal Addr ; 
               | bne Reg , Reg , Addr ; [strict (1 2)]
               | beq Reg , Reg , Addr ; [strict (1 2)]
               | bltz Reg , Addr ; [strict (1)]
               | bgtz Reg , Addr ; [strict (1)]
               | blez Reg , Addr ; [strict (1)]
               | bgez Reg , Addr ; [strict (1)]
               | lw Reg , Off ( Reg ) ; [strict (3)]
               | lw Reg , ( Reg + Reg ) ; [strict (2 3)]
               | lui Reg , Imm ;
               | sw Reg , Off ( Reg ) ; [strict (3)]
               | sw Reg , ( Reg + Reg ) ; [strict (2 3)]
               | nop ;
               | add.s FReg , FReg , FReg ; [strict (2 3)]
               | add.d FReg , FReg , FReg ; [strict (2 3)]
               | sub.s FReg , FReg , FReg ; [strict (2 3)]
               | sub.d FReg , FReg , FReg ; [strict (2 3)]
               | mul.s FReg , FReg , FReg ; [strict (2 3)]
               | mul.d FReg , FReg , FReg ; [strict (2 3)]
               | div.s FReg , FReg , FReg ; [strict (2 3)]
               | div.d FReg , FReg , FReg ; [strict (2 3)]
	       | abs.s FReg , FReg ; [strict (2)]
	       | abs.d FReg , FReg ; [strict (2)]
	       | mov.s FReg , FReg ; [strict (2)]
	       | mov.d FReg , FReg ; [strict (2)]
	       | neg.s FReg , FReg ; [strict (2)]
	       | neg.d FReg , FReg ; [strict (2)]
	       | cvt.s.d FReg , FReg ; [strict (2)]
	       | cvt.s.w FReg , FReg ; [strict (2)]
	       | cvt.d.s FReg , FReg ; [strict (2)]
	       | cvt.d.w FReg , FReg ; [strict (2)]
	       | cvt.w.s FReg , FReg ; [strict (2)]
	       | cvt.w.d FReg , FReg ; [strict (2)]
--- bug	       | c.eq.s FReg , FReg ; [strict]
--- bug	       | c.eq.d FReg , FReg ; [strict]
	       | c.lt.s FReg , FReg ; [strict]
	       | c.lt.d FReg , FReg ; [strict]
	       | c.le.s FReg , FReg ; [strict]
	       | c.le.d FReg , FReg ; [strict]
	       | sqrt.s FReg , FReg ; [strict (2)]
	       | sqrt.d FReg , FReg ; [strict (2)]
               | lui Reg , Imm ; 
               | mfc1 Reg , FReg ; [strict (2)]
	       | mtc1 Reg , FReg ; [strict (2)]


syntax Helpers ::= update ( K , K ) [strict(1)]
		 | incPC ( K ) [strict]
		 | setPC ( K , K ) [strict(2)]
                 | updMem ( K ) [strict]
                 

syntax K ::= Instr | Imm | Amt | Addr | Off | Helpers 

syntax Prog ::= Map

endkm

