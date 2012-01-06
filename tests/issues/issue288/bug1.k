module  BUG1-SYNTAX

  syntax Exp ::= #Int
               | Exp "+" Exp [prec(33) gather(E e) seqstrict]
	   
  syntax Pgm ::= "program" Exp ";"
		  
  syntax K ::= Exp		  
  
end module
		  
module  BUG1 
  imports  BUG1-SYNTAX
		    
 //  configuration <T> <k> $PGM:Pgm </k> <state> .Map </state> </T>

  syntax KResult ::= #Int
  
end module
