requires "json.md"

module JSON-TEST-SYNTAX
    imports STRING-SYNTAX
    imports JSON

    syntax Pgm ::= String | JSON
endmodule

module JSON-TEST
    imports JSON-TEST-SYNTAX

    configuration <k> $PGM:Pgm</k>
endmodule
