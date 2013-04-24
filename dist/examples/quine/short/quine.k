module QUINE

  configuration
    <out stream="stdout"> .List </out>
    <prefix> "module QUINE\n\n  configuration\n    <out stream=\"stdout\"> .List </out>\n" </prefix>
    <suffix> "\n  syntax\n    String ::= escape(String) [function]\n  rule\n    escape(S:String) => replaceAll(replaceAll(replaceAll(S, \"\\\\\", \"\\\\\\\\\"), \"\\n\", \"\\\\n\"), \"\\\"\", \"\\\\\\\"\")\n\n  rule\n    <prefix> Pre:String => . </prefix>\n    <suffix> Suf:String => . </suffix>\n    <out>... . => ListItem(Pre +String \"    <prefix> \\\"\" +String escape(Pre) +String \"\\\" </prefix>\\n\" +String \"    <suffix> \\\"\" +String escape(Suf) +String \"\\\" </suffix>\\n\" +String Suf) </out>\nendmodule\n" </suffix>

  syntax
    String ::= escape(String) [function]
  rule
    escape(S:String) => replaceAll(replaceAll(replaceAll(S, "\\", "\\\\"), "\n", "\\n"), "\"", "\\\"")

  rule
    <prefix> Pre:String => . </prefix>
    <suffix> Suf:String => . </suffix>
    <out>... . => ListItem(Pre +String "    <prefix> \"" +String escape(Pre) +String "\" </prefix>\n" +String "    <suffix> \"" +String escape(Suf) +String "\" </suffix>\n" +String Suf) </out>
endmodule
