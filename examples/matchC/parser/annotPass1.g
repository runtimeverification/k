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
  : id=IDENTIFIER { Table.progIdentifiers.contains($id.text) }?
    -> ^(IDENTIFIER["?var"] ^(ID["id"] STRING_LITERAL["\"" + $id.text + "\""]))
  ;

