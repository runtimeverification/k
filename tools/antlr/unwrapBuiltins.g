lexer grammar unwrapBuiltins;

options { filter = true; }

fragment
BUILTIN
  : 'MathObj++'
  | 'List`{MathObj++`}'
  | 'Formula'
  | 'Subst'
  | 'ExpressionType'
  | 'TypedValue'
  | 'Value'
  | 'Id'
  | 'Field'
  | 'HeapLabel'
;

BUILTIN_WRAPPER
  : APP '(' BUILTIN '_' '(' BUILTIN_CONTENT ')' ',' UNIT ')'
    { System.out.print($BUILTIN_CONTENT.text); }
  ;

CHAR
  : . { System.out.print($text); }
  ;

fragment
BUILTIN_CONTENT
  : ( ('(')=> '(' BUILTIN_CONTENT ')'
    | (~')')=> .
    )*
  ;

fragment
APP : '_`(_`)' ;

fragment
UNIT : '.List`{K`}' ;
