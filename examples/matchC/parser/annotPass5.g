tree grammar annotPass5;

options {
  tokenVocab = annot;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}


@members {
  String prefix = annotParser.annotType == annotParser.RULE ? "?" : "!";
  String rename(String name) { return prefix + name; }
}


bottomup
  : logical_variable
  ;

logical_variable
  : lv=LOGICAL_VARIABLE
    { !Table.annotLogicalVariables.contains($lv.text)
      && !($lv.text.startsWith("?") || $lv.text.startsWith("!")) }?
    { Table.annotIdentifiers.add(rename($lv.text)); }
    -> LOGICAL_VARIABLE[rename($lv.text)]
  ;

