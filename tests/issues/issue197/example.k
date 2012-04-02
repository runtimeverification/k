
module ISSUE is
	
	syntax Exp ::= Int | Exp + Exp
	syntax List{Exp} ::= Exp | () | Exp , Exp [strict assoc hybrid id: ()]
	syntax K ::= test1 | test2
	
	rule test1 => 5 , 7 , 8, 9 [structural]
	
	// Warning: sort declarations for constant '_`,_ do not have an unique least sort.
	rule '_`,_(5,, 7) => 13 [structural]
	
	// Advisory: <automatic>: collapse at top of E1:List{Exp},E2:List{Exp} may cause it to match more than you expect.
	rule E1:Exp , ?:Exp => E1:Exp [structural]
	
end module
