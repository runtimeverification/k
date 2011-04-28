tree grammar annotPass2;

options {
  tokenVocab = annot;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}


bottomup
  : relation
  ;

relation
  : ^(LT o1=. o2=.) -> ^(BUILTIN["@_"] ^(LT $o1 $o2))
  | ^(LEQ o1=. o2=.) -> ^(BUILTIN["@_"] ^(LEQ $o1 $o2))
  | ^(GT o1=. o2=.) -> ^(BUILTIN["@_"] ^(GT $o1 $o2))
  | ^(GEQ o1=. o2=.) -> ^(BUILTIN["@_"] ^(GEQ $o1 $o2))
  ;

