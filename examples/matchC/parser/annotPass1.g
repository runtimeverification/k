tree grammar annotPass1;

options {
  tokenVocab = annot;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}

@header {
  import java.util.HashSet;
}

@members {
  HashSet<String> mark = new HashSet<String>();
}

topdown
  : progam_identifier
  ;

progam_identifier
  : id=IDENTIFIER
    { Table.identifiers.contains($id.text) && !mark.contains($id.text) }?
    { mark.add($id.text); }
    -> ^(IDENTIFIER["?var"] $id)
  ;

