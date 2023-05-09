module CONFIG-SYNTAX
endmodule

module CONFIG
    imports INT
    configuration
        <T>
            <first> $FST:Int </first>
            <second> $SND:Int </second>
        </T>
endmodule
