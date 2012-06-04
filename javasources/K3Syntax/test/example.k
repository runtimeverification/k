module NOT-FL-SYNTAX


  syntax KLabel ::= "not#e"
		  | "not#H"


  syntax KResult ::= Int | Bool
  
  configuration asf


endmodule




module NOT-FL
   imports NOT-FL-SYNTAX


// NOT


  rule not#e(E1) => E1 ~> not#H(.List{K})
       when 'notBool('isKResult(E1))


  rulen E1 ~> not#H(.List{K}) => not#e(E1) 
       when 'isKResult(E1)


endmodule