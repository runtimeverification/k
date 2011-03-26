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
//  : { Table.progIdentifiers.contains(((CommonTree) input.LT(1)).getText())
//      && !Table.funIdentifiers.contains(((CommonTree) input.LT(1)).getText()) }?=>
  :  id=IDENTIFIER
     { Table.progIdentifiers.contains($id.text)
       && !Table.funIdentifiers.contains($id.text) }?
    -> ^(IDENTIFIER["?var"] ^(ID["id"] STRING_LITERAL["\"" + $id.text + "\""]))
//  | { Table.funIdentifiers.contains(input.LT(1).getText()) }?=>
  | id=IDENTIFIER
    { Table.funIdentifiers.contains($id.text) }?
    -> ^(ID["id"] STRING_LITERAL["\"" + $id.text + "\""])
  ;

