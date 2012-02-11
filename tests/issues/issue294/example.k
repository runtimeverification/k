module ISSUE 
	syntax K ::= test1 "(" #Int "," #Nat ")" | test2
	rule test1(I:#Int, N:#Nat) => test2 
		when I:#Int +Nat N:#Nat >=Int N:#Nat
		[structural]
end module

