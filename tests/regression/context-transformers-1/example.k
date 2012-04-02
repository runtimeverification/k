
module CONTEXT-TRANSFORMERS-TEST
  configuration
    <T>  
      <threads> <thread multiplicity="*"> <k> .K </k> </thread> </threads> 
      <out> .List </out>
    </T>

  syntax K ::= Int | print Int

  rule <k> print I:Int => . <_/k> <out_> . => ListItem(I) </out>


  syntax Bag ::= start | end

  rule start => <T> <threads> 
                      <thread> <k> print 5 </k> </thread> 
                      <thread> <k> .K </k> </thread> 
                    </threads> 
                    <out> .List </out> 
                </T>

  rule <T_> <out> ListItem(5) </out> <_/T> => end
end module

