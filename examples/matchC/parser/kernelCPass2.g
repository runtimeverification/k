tree grammar kernelCPass2;


options {
  tokenVocab = kernelC;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}


bottomup
  : typed_value
  ;

typed_value
  : IDENTIFIER -> ^(ID STRING_LITERAL["\"" + $IDENTIFIER.text + "\""])
  ;

