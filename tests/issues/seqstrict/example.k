
module ISSUE
	syntax K ::= K ; K [seqstrict transition]
                   | halt K

        rule <k> halt K:K ~> _:K => K </k> 
        
        syntax Bag ::= start | good | bad
        rule start => <k> (halt 'a(.List{K})) ; (halt 'b(.List{K})) </k>
        rule <k> 'a(.List{K}) </k> => good
        rule <k> 'b(.List{K}) </k> => bad
end module
