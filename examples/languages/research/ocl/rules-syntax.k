require ocl-syntax
// syntax of rules. A rule has the form
// from LHS when(Condition) using(LocalVariablesDeclaration) to RHS do (Program)

module RULES-SYNTAX 
  imports OCL-SYNTAX 

syntax Ids ::= List{#Id,","} [strict]

syntax Pgm ::= "var" Ids ";" Stmt

syntax Stmt ::= #Id "<-" Exp [strict(2)]  // local var assignment
				| Exp "@" #Id "<-" Exp [strict(1 3)]
				| "for" #Id "<-" Exp "{" Stmt "}"  [strict(2)] // for loop
				| "if" Exp "then" "{" Stmt "}" [strict(1)] 
				| "if" Exp "then" "{" Stmt "}" else "{" Stmt "}" [strict(1)] 
				| "print" "(" Exp ")" [strict]
				| Stmt ";"  Stmt
				| "skip"
				| "call" "(" #Id ")"

// conditions: evaluated by "when" clause
syntax K ::= "when" "(" Exp ")" [strict]

//update
syntax K ::= "update" "(" Bag ")" 

//using
syntax K ::= "using" "(" Pgm ")"

// do
syntax K ::= "do" "(" Pgm ")"

end module
