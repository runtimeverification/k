module STRING-REWRITE-SYNTAX
    imports STRING-SYNTAX
endmodule

module STRING-REWRITE
    imports STRING-REWRITE-SYNTAX
    imports STRING

    configuration <k> $PGM:String </k>
                  <s> "" </s>

    rule <k> S => .K ... </k>
         <s> _ => S      </s>
endmodule
