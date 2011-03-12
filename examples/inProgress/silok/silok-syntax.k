require ../../../k-prelude


kmod SILOK-SYNTAX is including PL-ID
  
  syntax ListId ::= .ListId | Id | ListId `, ListId [assoc id: .ListId strict hybrid] 

  syntax Pgm ::= gvars: ListId lvars: ListId { Procs }

  syntax Procs ::= ProcId :: B [prec 55 gather(e E)]
  	 	   | Procs Procs [prec 60 gather(e E)]

  syntax ProcId ::= main | breakpoint | p0 | p1 | p2 | p3 | p4

  syntax Id ::= new  

  syntax BExp ::= Id = Id [prec 43] | Id /= Id [prec 43]

  syntax B ::= Id := Id		      	 [prec 45 ]
  	       | B ; B 	     		 [prec 50 gather(e E)] 
  	       | [ BExp ] B 		 [prec 45]
	       | B + B 	   	  	 [prec 48]
	       | ProcId

endkm
