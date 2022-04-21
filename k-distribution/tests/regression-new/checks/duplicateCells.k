module DUPLICATERULES-SYNTAX
  imports DEFAULT-CONFIGURATION

    configuration <test> $TST:Int</test>

endmodule

module DUPLICATECELLS
    imports DUPLICATERULES-SYNTAX

    configuration <k> $PGM:Int </k>
                  <test> $TST:Int</test>

endmodule
