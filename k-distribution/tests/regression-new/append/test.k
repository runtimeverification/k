module TEAL-SYNTAX
  import INT-SYNTAX
endmodule

module TEST-SYNTAX
  imports TEAL-SYNTAX
endmodule

module TEST
  imports TEAL-SYNTAX

  configuration
      <k> $PGM:Int </k>
endmodule
