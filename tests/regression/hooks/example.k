module ISSUE 
	syntax K ::= K "+" K [hook(#INT:_+Int_ #FLOAT:_+Float_)]
        syntax Bag ::= "test1" | "test2" | "good"
        rule test1 => <k> 3 + 5 </k>
        rule test2 => <k> 3.2 + 5.7 </k>
        rule <k> 8 </k> => good
        rule <k> F:#Float </k> => good 
end module
