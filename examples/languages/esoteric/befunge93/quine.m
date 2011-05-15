load befunge-compiled
mod BEFUNGE-TEST is
	including BEFUNGE .
	
	--- equivalent to a quine found on http://esolangs.org/wiki/Befunge
	op quine : -> KProperLabel [metadata "arity 0"] .
	eq quine = injectM( __((.).Map,((.).Map 
	'coord`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K})) |-> String "0"(.List{K})
	'coord`(_`,_`)(Int 1(.List{K}),, Int 0(.List{K})) |-> String "1"(.List{K})
	'coord`(_`,_`)(Int 2(.List{K}),, Int 0(.List{K})) |-> String "-"(.List{K})
	'coord`(_`,_`)(Int 3(.List{K}),, Int 0(.List{K})) |-> String ">"(.List{K})
	'coord`(_`,_`)(Int 4(.List{K}),, Int 0(.List{K})) |-> String "1"(.List{K})
	'coord`(_`,_`)(Int 5(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 6(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 7(.List{K}),, Int 0(.List{K})) |-> String "+"(.List{K})
	'coord`(_`,_`)(Int 8(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 9(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 10(.List{K}),, Int 0(.List{K})) |-> String ":"(.List{K})
	'coord`(_`,_`)(Int 11(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 12(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 13(.List{K}),, Int 0(.List{K})) |-> String "0"(.List{K})
	'coord`(_`,_`)(Int 14(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 15(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 16(.List{K}),, Int 0(.List{K})) |-> String "g"(.List{K})
	'coord`(_`,_`)(Int 17(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 18(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 19(.List{K}),, Int 0(.List{K})) |-> String ","(.List{K})
	'coord`(_`,_`)(Int 20(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 21(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 22(.List{K}),, Int 0(.List{K})) |-> String ":"(.List{K})
	'coord`(_`,_`)(Int 23(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 24(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 25(.List{K}),, Int 0(.List{K})) |-> String "5"(.List{K})
	'coord`(_`,_`)(Int 26(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 27(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 28(.List{K}),, Int 0(.List{K})) |-> String "8"(.List{K})
	'coord`(_`,_`)(Int 29(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 30(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 31(.List{K}),, Int 0(.List{K})) |-> String "*"(.List{K})
	'coord`(_`,_`)(Int 32(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 33(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 34(.List{K}),, Int 0(.List{K})) |-> String "4"(.List{K})
	'coord`(_`,_`)(Int 35(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 36(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 37(.List{K}),, Int 0(.List{K})) |-> String "+"(.List{K})
	'coord`(_`,_`)(Int 38(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 39(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 40(.List{K}),, Int 0(.List{K})) |-> String "-"(.List{K})
	'coord`(_`,_`)(Int 41(.List{K}),, Int 0(.List{K})) |-> String "#"(.List{K})
	'coord`(_`,_`)(Int 42(.List{K}),, Int 0(.List{K})) |-> String " "(.List{K})
	'coord`(_`,_`)(Int 43(.List{K}),, Int 0(.List{K})) |-> String "_"(.List{K})
	'coord`(_`,_`)(Int 44(.List{K}),, Int 0(.List{K})) |-> String "@"(.List{K})
))) .

endm
rew eval(quine(.List{K})) .