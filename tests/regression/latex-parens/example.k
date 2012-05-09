module ISSUE 
	syntax K ::= test
	rule test => #if (3 *Int (4 +Int 5) -Int 7) /Int 2 ==Int 3 +Int 5 
                     #then '_*Int_('_+Int_('_-Int_(3,,7),,2),,0)
                     #else ('f(1,,3) +Int 8) *Int 7
                     #fi 
end module
