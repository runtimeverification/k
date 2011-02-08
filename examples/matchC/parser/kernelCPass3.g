tree grammar kernelCPass3;

options {
  tokenVocab = kernelC;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}


bottomup
  : annot
  ;

annot
  : ANNOTATION
  -> K[AnnotPreK.annotToMaudeString($ANNOTATION.text)]
  ;

