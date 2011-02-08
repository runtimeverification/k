tree grammar kernelCPass1;


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
  : STRING_LITERAL -> ^(TV STRING_TYPE STRING_LITERAL)
  | DECIMAL_LITERAL -> ^(TV INT_TYPE DECIMAL_LITERAL)
  | OCTAL_LITERAL -> ^(TV INT_TYPE OCTAL_LITERAL)
  | HEX_LITERAL -> ^(TV INT_TYPE HEX_LITERAL)
  | VOID_EXP -> ^(TV VOID_TYPE UNIT_EXP)
  ;


