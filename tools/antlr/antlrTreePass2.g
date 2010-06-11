tree grammar antlrTreePass2;

options { tokenVocab = antlr; output = AST; ASTLabelType=CommonTree; }

config
    : term
;

term
    : nklist
    | klist
;

nklist
    : ^('_`(_`)' term
      ( '.List`{K`}' -> term
      | nklist -> ^(term nklist)
      | ^('_`,`,_' term*) -> ^(term term*)
      )
    )
    | ^(op term*)
;

klist
    : '.List`{K`}'
    | ^('_`,`,_' term*)
;

op
    : ID
;
