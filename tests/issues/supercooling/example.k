
kmod ISSUE is
    tags nerd local
	syntax K ::= K + K [strict nerd]
                  | print K [strict]
                  | test
        
        syntax KResult ::= #Int

        configuration <k> .K </k> <out> .List </out>


  rule <k> print I:#Int => 0 ...</k> <out>... . => ListItem(I) </out> [local]
  rule 0 + 0 => 0



  macro test = print 1 + (print 2 + print 3)



     syntax Bag ::= start | end 
   rule start => <k> test </k> <out> . </out>
   rule <k> K:K </k> <out> ListItem(2) ListItem(1) ListItem(3) </out> => end
endkm
