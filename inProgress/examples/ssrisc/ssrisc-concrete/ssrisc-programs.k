kmod SSRISC-PROGRAMS is including SSRISC-SYNTAX + K

syntax Reg ::= a0 | a1 | a2 | ra | s8 | sp | v0 | v1 | zero

syntax Map ::= main1 | main2 | main3 | main4 | main5

macro main5 = 

--- 1016 |->( lw v0,(v1 + v1);)
1016 |->( sw v0,20(sp);)
1020 |->( sw v1,20(sp);)


***(
int i = 1;
int j = 10;
int sum = 0;
while (j < i)
  sum = sum + i;
  i = i + 1;
***)
macro main1 =

 1016 |->( addiu   v0,zero,1;)
 1020 |->( sw   v0,16(s8);) 
 1024 |->( addiu   v0,zero,3;)
 1028 |->( sw   v0,20(s8);)
 1032 |->( sw   zero,24(s8);)
 1036 |->( lw   v0,20(s8);)
 1040 |->( lw   v1,16(s8);)
 1044 |->( slt   v0,v1,v0;)
 1048 |->( bne   v0,zero,1056;)
 1052 |->( j   1088;)
 1056 |->( lw   v0,24(s8);)
 1060 |->( lw   v1,16(s8);)
 1064 |->( addu   v0,v0,v1;)
 1068 |->( sw   v0,24(s8);)
 1072 |->( lw   v0,16(s8);)
 1076 |->( addiu   v1,v0,1;)
 1080 |->( sw   v1,16(s8);)
 1084 |->( j   1036;)


macro main2 = 

 1016 |->( sw   zero,40(s8);)
 1020 |->( sw   zero,44(s8);)
 1024 |->( sw   zero,48(s8);)
 1028 |->( addiu   v0,zero,1;)
 1032 |->( sw   v0,16(s8);)
 1036 |->( addiu   v0,zero,4;)
 1040 |->( sw   v0,20(s8);)
 1044 |->( addiu   v0,zero,5;)
 1048 |->( sw   v0,24(s8);)
 1052 |->( addiu   v0,zero,2;)
 1056 |->( sw   v0,28(s8);)
 1060 |->( addiu   v0,zero,4;)
 1064 |->( sw   v0,32(s8);)
 1068 |->( sw   zero,48(s8);)
 1072 |->( lw   v0,48(s8);)
 1076 |->( slti   v1,v0,5;)
 1080 |->( bne   v1,zero,1084;)
 1084 |->( nop;)

***(
int x = 10;
int y = 2;
int sum = x + y;
***)

macro main3 = 

 1016 |->( addiu   v0,zero,10;)
 1020 |->( sw   v0,16(s8);)
 1024 |->( addiu   v0,zero,2;)
 1028 |->( sw   v0,20(s8);)
 1032 |->( lw   v0,16(s8);)
 1036 |->( lw   v1,20(s8);)
 1040 |->( addu   v0,v0,v1;)
 1044 |->( sw   v0,24(s8);)

***(
int sum = 5;
int i = 3;
if (sum > i)
  sum = sum + i;
***)

macro main4 = 

 1016 |->( addiu   v0,zero,5;)
 1020 |->( sw   v0,16(s8);)
 1024 |->( addiu   v0,zero,3;)
 1028 |->( sw   v0,20(s8);)
 1032 |->( lw   v0,16(s8);)
 1036 |->( lw   v1,20(s8);)
 1040 |->( slt   v0,v1,v0;)
 1044 |->( beq   v0,zero,1064;)
 1048 |->( lw   v0,16(s8);)
 1052 |->( lw   v1,20(s8);)
 1056 |->( addu   v0,v0,v1;)
 1060 |->( sw   v0,16(s8);)

endkm

