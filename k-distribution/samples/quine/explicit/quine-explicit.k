// Copyright (c) 2013-2015 K Team. All Rights Reserved.
/*!
\title{A quine program written in K-framwork}
\author{Radu Mereu\c{t}\u{a}
        (\texttt{radu.mereuta@info.uaic.ro})}
\organization{University of Al. I. Cuza, Ia\c{s}i}
*/
//@Usage: kompile and then run with krun --output none
module QUINE-EXPLICIT

  configuration
    <k> "" ~> "" </k>
    <out stream="stdout"> .List </out>
    <prefix>
        "// Copyright (c) 2013-2014 K Team. All Rights Reserved." ~>
        "/*!" ~>
        "\\title{A quine program written in K-framwork}" ~>
        "\\author{Radu Mereu\\c{t}\\u{a}" ~>
        "        (\\texttt{radu.mereuta@info.uaic.ro})}" ~>
        "\\organization{University of Al. I. Cuza, Ia\\c{s}i}" ~>
        "*/" ~>
        "//@Usage: kompile and then run with krun --output none" ~>
        "module QUINE-EXPLICIT" ~>
        "" ~>
        "  configuration" ~>
        "    <k> \"\" ~> \"\" </k>" ~>
        "    <out stream=\"stdout\"> .List </out>" ~>
        "    <prefix>" ~>
        .K
    </prefix>
    <suffix>
        "" ~>
        "  syntax" ~>
        "    K ::= escape(String) [function]" ~>
        "  rule" ~>
        "    escape(S:String) => replaceAll(replaceAll(replaceAll(S, \"\\\\\", \"\\\\\\\\\"), \"\\n\", \"\\\\n\"), \"\\\"\", \"\\\\\\\"\")" ~>
        "" ~>
        "  rule" ~>
        "    <k> (S1 => S1 +String P +String \"\\n\") ~> (S2 => S2 +String \"        \\\"\" +String escape(P) +String \"\\\" ~>\\n\") </k>" ~>
        "    <prefix> P:String => .K ...</prefix>" ~>
        "" ~>
        "  rule" ~>
        "    <k> S1 ~> S2 => \"\" ~> \"\" </k>" ~>
        "    <prefix> .K    => 0 </prefix>" ~>
        "    <out>... .List => ListItem(S1 +String S2 +String \"        .K\\n    </prefix>\\n    <suffix>\\n\") </out>" ~>
        "" ~>
        "  rule" ~>
        "    <k> (S1 => S1 +String P +String \"\\n\") ~> (S2 => S2 +String \"        \\\"\" +String escape(P) +String \"\\\" ~>\\n\") </k>" ~>
        "    <suffix> P:String => .K ...</suffix>" ~>
        "    <prefix> 0 </prefix>" ~>
        "" ~>
        "  rule" ~>
        "    <k> S1 ~> S2 => . </k>" ~>
        "    <suffix> .K    => 0 </suffix>" ~>
        "    <out>... .List => ListItem(S2 +String \"        .K\\n    </suffix>\\n\" +String S1) </out>" ~>
        "" ~>
        "endmodule" ~>
        .K
    </suffix>

  syntax
    K ::= escape(String) [function]
  rule
    escape(S:String) => replaceAll(replaceAll(replaceAll(S, "\\", "\\\\"), "\n", "\\n"), "\"", "\\\"")

  rule
    <k> (S1 => S1 +String P +String "\n") ~> (S2 => S2 +String "        \"" +String escape(P) +String "\" ~>\n") </k>
    <prefix> P:String => .K ...</prefix>

  rule
    <k> S1 ~> S2 => "" ~> "" </k>
    <prefix> .K    => 0 </prefix>
    <out>... .List => ListItem(S1 +String S2 +String "        .K\n    </prefix>\n    <suffix>\n") </out>

  rule
    <k> (S1 => S1 +String P +String "\n") ~> (S2 => S2 +String "        \"" +String escape(P) +String "\" ~>\n") </k>
    <suffix> P:String => .K ...</suffix>
    <prefix> 0 </prefix>

  rule
    <k> S1 ~> S2 => . </k>
    <suffix> .K    => 0 </suffix>
    <out>... .List => ListItem(S2 +String "        .K\n    </suffix>\n" +String S1) </out>

endmodule
