kmod SSRISC-SYNTAX is including PL-INT32 + PL-UNSIGNED-INT32 + PL-ID + PL-FLOAT + K 

syntax Reg ::= Val32 

syntax FReg ::= Float

syntax Imm ::= Val32

syntax Amt ::= Nat

syntax Addr ::= Val32 

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
               | lui Reg , Imm ;
               | lw Reg , Off ( Reg ) ; [strict (3)]
               | lw Reg , ( Reg + Reg ) ; [strict (2 3)]
               | sw Reg , Off ( Reg ) ; [strict (3)]
               | sw Reg , ( Reg + Reg ) ; [strict (2 3)]
               | nop ;

--- new stuff
               | jalr Reg 
               | lb Reg , Off ( Reg ) [strict (3)]
               | lb Reg , ( Reg  + Reg ) [strict (2 3)]
               | lbu Reg , Off ( Reg ) [strict (3)]
               | lbu Reg , ( Reg  + Reg ) [strict (2 3)]
               | lh Reg , Off ( Reg ) [strict (3)]
               | lh Reg , ( Reg  + Reg ) [strict (2 3)]
               | lhu Reg , Off ( Reg ) [strict (3)]
               | lbu Reg , ( Reg  + Reg ) [strict (2 3)]
               | dlw Reg , Off ( Reg ) [strict (3)]
               | dlw Reg , ( Reg  + Reg ) [strict (2 3)]
               | sb Reg , Off ( Reg ) [strict (3)]
               | sb Reg , ( Reg  + Reg ) [strict (2 3)]
               | sh Reg , Off ( Reg ) [strict (3)]
               | sh Reg , ( Reg  + Reg ) [strict (2 3)]
               | sw Reg , Off ( Reg ) [strict (3)]
               | sw Reg , ( Reg  + Reg ) [strict (2 3)]
               | dsw Reg , Off ( Reg ) [strict (3)]
               | dsw Reg , ( Reg  + Reg ) [strict (2 3)]
               | dsz Reg , Off ( Reg ) [strict (3)]
               | dsz Reg , ( Reg  + Reg ) [strict (2 3)]
--- remove subi
               | subu Reg , Reg , Reg ; [strict (2 3)]     
               | mult Reg , Reg ; [strict (1 2)]               
               | multu Reg , Reg ; [strict (1 2)]
               | div Reg , Reg ; [strict (1 2)]               
               | divu Reg , Reg ; [strict (1 2)]
               | mthi Reg ; [strict]               
               | mfhi Reg ; [strict]
               | mtlo Reg ; [strict]               
               | mflo Reg ; [strict]
               | and Reg , Reg , Reg ; [strict (2 3)]
	       | andi Reg , Reg , Imm ; [strict (2)]
               | or Reg , Reg , Reg ; [strict (2 3)]
	       | ori Reg , Reg , Imm ; [strict (2)]          
               | xor Reg , Reg , Reg ; [strict (2 3)]
	       | xori Reg , Reg , Imm ; [strict (2)]          
               | nor Reg , Reg , Reg ; [strict (2 3)]
	       | sllv Reg , Reg , Reg ; [strict (2 3)]
	       | srlv Reg , Reg , Reg ; [strict (2 3)]
	       | srav Reg , Reg , Reg ; [strict (2 3)]

syntax Helpers ::= update ( K , K ) [strict(1)]
		 | incPC ( K ) [strict]
		 | setPC ( K , K ) [strict(2)]
                 | updMem ( K ) [strict]
                 

syntax K ::= Instr | Imm | Amt | Addr | Off | Helpers 

syntax Prog ::= Map

endkm

