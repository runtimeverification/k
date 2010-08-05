kmod P-LIST-COPY is including IMP-SYNTAX + LIST-HP
	syntax Id ::= a | b | next | i | x | y | copy | nodeList | val 
	syntax ?Int ::= `?b | `?i | `?x | `?v | `?y | `?w | `?a
	syntax FreeInt ::= `a0 
	syntax ?Seq ::= `?A | `?B | `?X | `?A'
	syntax FreeSeq ::= `A 

	syntax Decl ::= pListCopy

	macro pListCopy = (
 
 struct nodeList {
   int val;
   struct nodeList *next;
 };
 
 int copy(struct nodeList *a;)
 // pre <config> 
         <env> a |-> [a0 : &struct nodeList] </env>
         <heap> list(a0)(A) </heap> 
         <form> ~(a0 === 0) </form>
         </config>
         
 // post <config> 
                   <env> a |-> [a0 : &struct nodeList]  b |-> [?b : &struct nodeList] x |-> [?x : &struct nodeList] i |-> [?b : int] y |-> [?y : &struct nodeList] </env>
                   <heap> 
                        list(?x)(?X) 
                        a0|-> ?v : [val : int ]  (a0 +Int 1) |-> ?x : [next : &struct nodeList] 
                        ?b |-> ?v : [val : int ]  (?b +Int 1) |-> 0 : [next : &struct nodeList] 
                        ?y |-> ?w : [val : int ]  (?y +Int 1) |-> 0 : [next : &struct nodeList]
                        </heap> 
                   <form> ([?v] ::: ?X === A) </form> 
                   </config>
 {
 struct nodeList *b;
 int i ;
 b = new struct nodeList ;
  if (a == 0) 
  {
  i = 0 ;
   b->val = a->val ;
   b->next = 0 ;
   
   struct nodeList *x;
   x = a->next;
   
   struct nodeList *y ;
   y = new struct nodeList ;
  }
  else
  {
   i = b ;
   b->val = a->val ;
   b->next = 0 ;
   
   struct nodeList *x;
   x = a->next;
   
   struct nodeList *y ;
   y = new struct nodeList ;
   }
   return i ;
 }

)
endkm