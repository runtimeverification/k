kmod TEST is including IMP-SYNTAX + LIST-HP
	syntax Id ::= a | b | c | sum | res
	syntax ?Int ::= `?res
	syntax FreeInt ::= `a0 | `b0
	syntax ?Int ::= `?a | `?b | `?c
	--- syntax FreeSeq ::= none

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
 
 void main()
 {
/* assume <config> 
         <env> (.).Map </env>
         <heap> (.).Map </heap> 
         <form> TrueFormula </form>
         </config> */
  int a;
  int b;
  a = 5;
  b = 6;
  int c;
  sum(?a, ?b) ;
/* assert <config> 
                   <env> a |-> [?a : int]  b |-> [?b : int]   c |-> [?c : int ] </env>
                   <heap> (.).Map </heap> 
                   <form> (?c === ?a +Int ?b) </form> 
                   </config> */
 }

)
endkm