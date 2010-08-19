kmod TEST is including IMP-SYNTAX + LIST-HP
	syntax Id ::= a | b | res | maximum
	syntax ?Int ::= `?res
	syntax FreeInt ::= `a0 | `b0
	syntax ?Int ::= `?a | `?b

	syntax Decl ::= test

	macro test = (
 
 int maximum(int a; int b;)
 /* pre <config> 
         <env> a |-> [a0 : int] b|-> [b0 : int] </env>
         <heap> (.).Map </heap> 
         <form> ~(a0 === 0) /\ ~(b0 === 0) </form>
         </config> */
         
 /* post <config> 
                   <env> a |-> [a0 : int] b |-> [b0 : int] res |-> [?res : int ] </env>
                   <heap> (.).Map </heap> 
                   <form> ?return(?res) /\ ( (?res === a0) \/ (?res === b0)) </form> 
                   </config> */
 {
 int res;
  if (a > b) res = a;
  else res = b;
  return res;
 }

)
endkm