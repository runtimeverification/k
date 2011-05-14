
kmod IDRLS is
	including K + PL-BOOL + PL-INT + PL-ID
	
	syntax Exp ::= Id | Val | Exp + Exp
	syntax Val ::= Int | Bool
        syntax KResult ::= Val
        syntax K ::= Exp

        syntax Id ::= a | b | c
        rule a + b => a
        rule a + b => a
endkm
