module ISSUE
  configuration <T>
                  <thread multiplicity="*">
                        <k> $PGM:K </k>
                        <holds> .Map </holds>
                  </thread>
		</T>
				
  syntax K ::= "spawn"

  rule <k> spawn => . ...</k>
	   (. => 
            <thread>
              ...
              <k> .K </k>
            </thread>
           )

  rule <k> spawn => . ...</k>
	   (. => 
            <thread>
              <k> .K </k>
              ...
            </thread>
           )

  rule <k> spawn => . ...</k>
	   (. => 
            <thread>
              ...
              <k> .K </k>
              ...
            </thread>
           )
endmodule
