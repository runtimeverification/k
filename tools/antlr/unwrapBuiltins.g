grammar unwrapBuiltins;


tokens {
    CONTENT;
    BUILTIN;
    APP = '_`(_`)';
    UNIT = '.List`{K`}';
    LPAREN = '(';
    RPAREN = ')';
    COMMA = ',';
    USCORE = '_';
}



@members {
  boolean isWrapper = false;
  int count;
  String wrappedBuiltin;
}

module : (begin | end | content)* ;

begin
  : APP '(' BUILTIN '_' '('
  { isWrapper = true; count = 0; wrappedBuiltin = ""; }
  | APP (~'(' | '(' ~BUILTIN)
  {
    if (isWrapper) wrappedBuiltin += $text;
    else System.out.print($text);
  }
;

end
  : { isWrapper && count == 0 }? ')' ',' UNIT ')'
  { isWrapper  = false; System.out.print(wrappedBuiltin + " "); }
  | { !(isWrapper && count == 0) }? ')'
  {
    if (isWrapper)
    {
      count--;
      wrappedBuiltin += $text;
    }
    else System.out.print($text);
  }
;

content
@after
{
  if (isWrapper) wrappedBuiltin += $text;
  else System.out.print($text);
}
  : '(' { if (isWrapper) count++; }
  | BUILTIN
  | CONTENT
  | UNIT
  | '_'
  | ','
;


BUILTIN
  : 'IntSymbolic'
  | 'Id'
;

CONTENT
  : '_'?  ~('(' | ')' | ',' | '_')*
  | '_`(`)'
;

