module TREE-TS-SYNTAX
    imports STRING-SYNTAX
endmodule

module TREE-TS
    imports TREE-TS-SYNTAX

    configuration <k> "" </k>

    rule <k> "" => "a" </k>
    rule <k> "" => "b" </k>
    rule <k> "a" => "aa" </k>
    rule <k> "a" => "ab" </k>
    rule <k> "b" => "ba" </k>
    rule <k> "b" => "bb" </k>
    rule <k> "aa" => "aaa" </k>
    rule <k> "aa" => "aab" </k>
    rule <k> "ab" => "aba" </k>
    rule <k> "ab" => "abb" </k>
    rule <k> "ba" => "baa" </k>
    rule <k> "ba" => "bab" </k>
    rule <k> "bb" => "bba" </k>
    rule <k> "bb" => "bbb" </k>
endmodule
