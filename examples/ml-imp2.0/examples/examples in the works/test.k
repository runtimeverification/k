kmod TEST is including IMP-SYNTAX + LIST-HP
	syntax Id ::= a | b | c | d | multiplicatin-by-addition | res | maximum
	syntax ?Int ::= `?res
	syntax FreeInt ::= `a0 | `b0
	syntax ?Int ::= `?a | `?b | `?c | `?d
	--- syntax FreeSeq ::= none

	syntax Decl ::= test

	macro test = (
 
 
 int multiplicatin-by-addition(int a; int b;)
 /* pre <config> 
         <env> a |-> [a0 : int] b|-> [b0 : int] </env>
         <heap> (.).Map </heap> 
         <form> TrueFormula </form>
         </config> */
         
 /* post <config> 
              <env> a |-> [a0 : int] b |-> [b0 : int] c |-> [?c : int] res |-> [a0 *Int b0 : int ] </env>
              <heap> (.).Map </heap> 
              <form> ?return(a0 *Int b0) /\ (?c === b0)</form> 
              </config> */
 {
 int c;
 c = 0;
 int res;
 res = 0;
 /* invariant <config>
                     <env> a |-> [a0 : int] b |-> [b0 : int] c |-> [?c : int] res |-> [a0 *Int ?c : int ] </env>
                     <heap> (.).Map </heap> 
                     <form> TrueFormula </form> 
                     </config> */ 
 while (!(b == c))
 {
    res = res + a;
    c = c + 1;
 }
 return res;
 }
 
  void main()
 {
/* assume <config> 
         <env> a |-> [a0 : int] b |-> [b0 : int] </env>
         <heap> (.).Map </heap> 
         <form> TrueFormula </form>
         </config> */
  int d ;
  d = multiplicatin-by-addition(a,,, b) ;
  breakpoint;
/* assert <config> 
                   <env> a |-> [a0 : int]  b |-> [b0 : int] d |-> [(a0 *Int b0) : int] </env>
                   <heap> (.).Map </heap> 
                   <form> TrueFormula </form> 
                   </config> */
 }
 
)
endkm