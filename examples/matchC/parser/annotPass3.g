tree grammar annotPass3;

options {
  tokenVocab = annot;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}


bottomup
  : default_k
  ;

default_k
  : ^(w=IDENTIFIER v=IDENTIFIER) { $w.text.equals("defaultKItem") }?
    -> ^(APP["_`(_`)"] KLABEL["'defaultKItem`(_`)"]
         ^(APP["_`(_`)"] ^(BUILTIN["List`{MathObj++`}_"] $v) K_LIST[".List{K}"])
       )
  ;

