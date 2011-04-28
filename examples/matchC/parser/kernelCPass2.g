tree grammar kernelCPass2;


options {
  tokenVocab = kernelC;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}


bottomup
  : identifier
  ;

identifier
  : IDENTIFIER -> ^(ID STRING_LITERAL["\"" + $IDENTIFIER.text + "\""])
  ;

