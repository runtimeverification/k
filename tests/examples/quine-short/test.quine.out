module QUINE-SHORT

  configuration
    <out stream="stdout"> .List </out>
    <prefix> "module QUINE-SHORT\n\n  configuration\n    <out stream=\"stdout\"> .List </out>\n" </prefix>
    <suffix> "\n  rule\n    <prefix> Pre:String => . </prefix>\n    <suffix> Suf:String => . </suffix>\n    <out>... . => ListItem(Pre +String \"    <prefix> \\\"\" +String replaceAll(replaceAll(replaceAll(Pre, \"\\\\\", \"\\\\\\\\\"), \"\\n\", \"\\\\n\"), \"\\\"\", \"\\\\\\\"\") +String \"\\\" </prefix>\\n\" +String \"    <suffix> \\\"\" +String replaceAll(replaceAll(replaceAll(Suf, \"\\\\\", \"\\\\\\\\\"), \"\\n\", \"\\\\n\"), \"\\\"\", \"\\\\\\\"\") +String \"\\\" </suffix>\\n\" +String Suf) </out>\nendmodule\n" </suffix>

  rule
    <prefix> Pre:String => . </prefix>
    <suffix> Suf:String => . </suffix>
    <out>... . => ListItem(Pre +String "    <prefix> \"" +String replaceAll(replaceAll(replaceAll(Pre, "\\", "\\\\"), "\n", "\\n"), "\"", "\\\"") +String "\" </prefix>\n" +String "    <suffix> \"" +String replaceAll(replaceAll(replaceAll(Suf, "\\", "\\\\"), "\n", "\\n"), "\"", "\\\"") +String "\" </suffix>\n" +String Suf) </out>
endmodule
