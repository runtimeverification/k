tree grammar annotPass1;

options {
  tokenVocab = annot;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}

bottomup
  : progam_identifier
  ;

progam_identifier
options { backtrack = true; }
  : id=IDENTIFIER
    { !Table.varString.startsWith("!")
      && Table.progIdentifiers.contains($id.text)
      && !Table.funIdentifiers.contains($id.text) }?
    //-> ^(IDENTIFIER["FreeVar"]
    -> ^(IDENTIFIER["?var"]
         ^(ID["id"] STRING_LITERAL["\"" + $id.text + "\""]))
  | id=IDENTIFIER
    { Table.varString.startsWith("!")
      && Table.progIdentifiers.contains($id.text)
      && !Table.funIdentifiers.contains($id.text) }?
    -> ^(IDENTIFIER["?var"] ^(ID["id"] STRING_LITERAL["\"" + $id.text + "\""]))
  | id=IDENTIFIER
    { Table.funIdentifiers.contains($id.text) }?
    -> ^(ID["id"] STRING_LITERAL["\"" + $id.text + "\""])
  | id=PRIME_IDENTIFIER
    -> ^(IDENTIFIER["?var"]
         ^(ID["id"] STRING_LITERAL["\"" + $id.text.replace("\'", "") + "\""]))
  | ^(old_wrapper=IDENTIFIER ^(var_wrapper=IDENTIFIER c=.))
    { "old".equals($old_wrapper.text) && "?var".equals($var_wrapper.text) }?
    -> ^(IDENTIFIER["FreeVar"] $c)
  ;

