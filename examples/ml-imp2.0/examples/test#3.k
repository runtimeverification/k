kmod TEST is including IMP-SYNTAX + LIST-HP
	syntax Id ::= a | b | c | square | res
	syntax ?Int ::= `?res
	syntax FreeInt ::= `a0 | `b0 | `c0
	syntax ?Int ::= `?a | `?b

	syntax Decl ::= test

	macro test = (
 
int square(int c;)
 /* pre <config> 
         <env> c |-> [c0 : int] </env>
         <heap> (.).Map </heap> 
         <form> TrueFormula </form>
         </config> */
         
 /* post <config> 
                   <env> c |-> [c0 : int] res |-> [(c0 *Int c0) : int ] </env>
                   <heap> (.).Map </heap> 
                   <form> ?return((c0 *Int c0)) </form> 
                   </config> */
 {
   int res;
   res = c * c;
   return res;
 }
 
 void main()
 {
/* assume <config> 
         <env> a |-> [a0 : int]  </env>
         <heap> (.).Map </heap> 
         <form> TrueFormula </form>
         </config> */
  int b ;
  b = square(a) ;
/* assert <config> 
                   <env> a |-> [a0 : int]  b |-> [(a0 *Int a0) : int]  </env>
                   <heap> (.).Map </heap> 
                   <form> TrueFormula </form> 
                   </config> */
 }

)
endkm
