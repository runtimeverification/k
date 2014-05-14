// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module QUINE-SHORT

  configuration
    <out stream="stdout"> .List </out>
    <prefix> "// Copyright (c) 2013-2014 K Team. All Rights Reserved.\nmodule QUINE-SHORT\n\n  configuration\n    <out stream=\"stdout\"> .List </out>\n" </prefix>
    <suffix> "\n  rule\n    <prefix> Pre:String => .K </prefix>\n    <suffix> Suf:String => .K </suffix>\n    <out>... .List => ListItem(Pre +String \"    <prefix> \\\"\" +String replaceAll(replaceAll(replaceAll(Pre, \"\\\\\", \"\\\\\\\\\"), \"\\n\", \"\\\\n\"), \"\\\"\", \"\\\\\\\"\") +String \"\\\" </prefix>\\n\" +String \"    <suffix> \\\"\" +String replaceAll(replaceAll(replaceAll(Suf, \"\\\\\", \"\\\\\\\\\"), \"\\n\", \"\\\\n\"), \"\\\"\", \"\\\\\\\"\") +String \"\\\" </suffix>\\n\" +String Suf) </out>\nendmodule\n" </suffix>

  rule
    <prefix> Pre:String => .K </prefix>
    <suffix> Suf:String => .K </suffix>
    <out>... .List => ListItem(Pre +String "    <prefix> \"" +String replaceAll(replaceAll(replaceAll(Pre, "\\", "\\\\"), "\n", "\\n"), "\"", "\\\"") +String "\" </prefix>\n" +String "    <suffix> \"" +String replaceAll(replaceAll(replaceAll(Suf, "\\", "\\\\"), "\n", "\\n"), "\"", "\\\"") +String "\" </suffix>\n" +String Suf) </out>
endmodule
