module TEST
    imports INT

    configuration <k> fresh </k>
    syntax KItem ::= "fresh"
    rule fresh => ?_:Int 
    
    syntax KItem ::= "odd"
    rule I => odd requires I %Int 2 ==Int 1
endmodule
