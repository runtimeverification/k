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
    -> ^(IDENTIFIER["FreeVar"]
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
 
  ;

