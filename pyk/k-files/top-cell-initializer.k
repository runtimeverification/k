module TOP-CELL-INITIALIZER-SYNTAX
    imports INT-SYNTAX
endmodule

module TOP-CELL-INITIALIZER
    imports TOP-CELL-INITIALIZER-SYNTAX
    configuration
        <k> $PGM:Int </k>
        <a> $A:Int </a>
        <b> $B:Int </b>
        <c> $C:Int </c>
endmodule
