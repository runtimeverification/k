module ISSUE
  configuration <T>
                  <control>
                     <k> $PGM:K </k>
                     <test> .List </test>
                  </control>
                  <out stream="stdout"> .List </out>
		</T>
  syntax K ::= "test"

  syntax K ::= control(ControlCellFragment)

  rule <control> C
        <k> test => control(C) ...</k>
       </control>

  rule <k> control(C) => . ...</k>
       <out>... . => ListItem("ok") </out>
endmodule
