require ../../../k-prelude


kmod SILOK-SYNTAX is including PL-ID
  
  syntax List{Id} ::= .List{Id} | Id | List{Id} , List{Id} [assoc id: .List{Id} strict hybrid] 

  syntax Pgm ::= gvars: List{Id} lvars: List{Id} { Procs }

  syntax Procs ::= ProcId :: B [prec 55 gather(e E)]
  	 	   | Procs Procs [prec 60 gather(e E)]

  syntax ProcId ::= main | breakpoint

  syntax Id ::= new  

  syntax BExp ::= Id = Id [prec 43] | Id /= Id [prec 43]

  syntax B ::= Id := Id		      	 [prec 45 ]
  	       | B ; B 	     		 [prec 50 gather(e E)] 
  	       | [ BExp ] B 		 [prec 45]
	       | B + B 	   	  	 [prec 48]
	       | ProcId

endkm
