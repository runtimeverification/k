module ISSUE 
	syntax K ::= "start1" | "start2" | "test1" [klabel(good)] | "test2" [klabel(middle)] 
        rule start1 => test1 [anywhere]
        rule start2 => test2 [anywhere]
        rule 'middle(.List{K}) => test1 [anywhere]
end module
