tree grammar antlrTreePass1;

options { tokenVocab = antlr; output = AST; ASTLabelType=CommonTree; }

config
    : term
;

term
    : ^('"Int"_' term) -> term
    | ^('"Id"_' term) -> term
    | ^(op term*)
;

op
    : ID
    | '.List`{K`}'
    | '_`(_`)'
    | '_`,`,_'
;
