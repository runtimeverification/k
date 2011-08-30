
kmod ISSUE is
    tags nerd local
	syntax K ::= K + K [strict(1) nerd]
                  |  K * K [strict nerd]
                  | print K [strict nerd]
                  | skip
                  | wrap ( K ) [strict nerd] 
                  | test

       context _ + ([#] => wrap([#])) [metadata "nerd=()"]

        rule <k> wrap(0) => 0 ...</k> [local]
        
        syntax KResult ::= #Int

        configuration <k> .K </k> <out> .List </out>


  rule <k> print sNat(N:#Nat) => print(N) ~> skip ...</k> <out>... . => ListItem(sNat(N)) </out> [local]
  rule <k> print 0 => 0 ...</k> <out>... . => ListItem(0) </out> [local]
  rule 0 + 0 => 0
  rule <k> 0 ~> skip => 0 ...</k>



  macro test = print 1 + (print 2 + print 3)



     syntax Bag ::= start | end 
   rule start => <k> test </k> <out> . </out>
   rule <k> K:K </k> <out> ListItem(2) ListItem(1) ListItem(3) </out> => end
endkm
