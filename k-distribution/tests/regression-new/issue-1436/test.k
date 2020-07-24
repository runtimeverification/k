module TEST-SYNTAX
    imports DOMAINS-SYNTAX
    syntax Prog ::= run(Int)
endmodule

module TEST
    imports TEST-SYNTAX
    imports DOMAINS

    syntax KResult

    configuration
        <k> $PGM:Prog </k>
        <bar> 6 </bar>
        <log stream="stdout"> .List </log>

    syntax Int ::= foo(Int) [function]

    rule [[ foo(0) => I ]]
         <bar> I </bar>

    rule <k> run(I) => foo(I) ...</k>
         <log>... .List => ListItem(I) </log>
endmodule
