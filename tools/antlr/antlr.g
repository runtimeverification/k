grammar antlr;

options { output = AST; }

config
    : term
;

term
    : op
    | '('! op ').'! ID!
    | op '(' termlist ')' -> ^(op termlist)
    | '(' op ').' ID '(' termlist ')' -> ^(op termlist)
;

termlist
    : term (','! term)*
;

op
    : ID
    | '.List`{K`}'
    | '_`(_`)'
    | '_`,`,_'
    | '"Int"_'
    | '"Id"_'
;

NEWLINE :'\r'? '\n' {skip();} ;
WS :   (' '|'\t')+ {skip();} ;
fragment
STRING : '\"' ('\\\"'|~('\\'|'\"'))* '\"' ;
fragment
SYM
    : '~'
    | '!'
    | '@'
    | '#'
    | '$'
    | '%'
    | '^'
    | '&'
    | '*'
    | '-'
    | '='
    | '+'
    | '\\'
    | '|'
    | ';'
    | ':'
    | '<'
    | '.'
    | '>'
    | '/'
    | '?'
;
fragment
ESC
    : '('
    |  ')'
    |  '['
    |  ']'
    |  '{'
    |  '}'
    |  ','
    |  ' '
;
ID : ('a'..'z'|'A'..'Z'|'0'..'9'|STRING|SYM|'`'ESC|'_')+ ;
