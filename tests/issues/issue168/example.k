
module IDRLS is
	
	syntax Exp ::= Id | Val | Exp + Exp
	syntax Val ::= Int | Bool
        syntax KResult ::= Val
        syntax K ::= Exp

        syntax Id ::= a | b | c
        rule a + b => a
        rule a + b => a
end module
