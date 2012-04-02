require "built-ins.k"

module MOD-SYNTAX
	
  syntax K ::= #Id "::" Bag
		     | "lookupMember" "(" BagItem "," #Id ")" [declare]
  // BagItem is the envStack cell, Id is the member name
  configuration <T> <env> .Map </env> </T>
  
  
  rule 'asdf(1) => 'aaaa(2)


// First look for the member in the top environment; if found then done.
  define lookupMember(<envStack> ListItem(_:#Id :: <env>...X|->L...</env>)
                    ...</envStack>,X) => .K  [structural]
// Otherwise, recurse through the object environment stack
  define lookupMember(<envStack> ListItem(_:#Id :: <env> Env </env>)
                            => . ...</envStack>, X)
	    when notBool(X in keys(Env))                      [structural]
	

endmodule
