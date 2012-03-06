module ISSUE 
  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <control color="cyan">
                        <k color="green"> $PGM:K </k>
                      </control>
                    </thread>
                  </threads>
                </T>

        syntax Bag ::= "start" | "good"
        syntax K ::= "rendezvous" 
        rule <k> rendezvous => . ...</k> <k> rendezvous => . ...</k>
        rule <thread>... <k> .K </k> ...</thread> => .
        rule <T> <threads> .Bag </threads> </T> => good
        rule start => 
             <T>
                  <threads>
                    <thread>
                      <control>
                        <k> rendezvous </k>
                      </control>
                    </thread>
                    <thread>
                      <control>
                        <k> rendezvous </k>
                      </control>
                    </thread>
                  </threads>
                </T>


end module
