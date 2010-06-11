tree grammar antlrTreePass3;

options { tokenVocab = antlr; output = AST; ASTLabelType=CommonTree; }

@members { boolean isApp; boolean isNil; }

config
    : term
;

term
@init { boolean isConst = false; }
    : op 
;

op
@init { isApp = false; isNil = false; }
    : ID
    | '.List`{K`}'
    | '_`,`,_'
;
