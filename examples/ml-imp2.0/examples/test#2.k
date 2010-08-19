kmod TEST is including IMP-SYNTAX + LIST-HP
	syntax Id ::= a | b | sum | res
	syntax ?Int ::= `?res
	syntax FreeInt ::= `a0 | `b0

	syntax Decl ::= test

	macro test = (
 
 int sum(int a; int b;)
 /* pre <config> 
         <env> a |-> [a0 : int] b |-> [b0 : int] </env>
         <heap> (.).Map </heap> 
         <form> TrueFormula </form>
         </config> */
         
 /* post <config> 
                   <env> a |-> [a0 : int]  b |-> [b0 : int] res |-> [?res : int ] </env>
                   <heap> (.).Map </heap> 
                   <form> ?return(?res) /\ (?res === a0 +Int b0) </form> 
                   </config> */
 {
   int res;
   res = a + b;
   return res;
 }

)
endkm