lexer grammar k;

tokens {
  APP;
  KLABEL;
  WRAPPER;
  K;
  BUILTIN;

  K_UNIT;
  K_ARROW;

  K_LIST;
  K_LIST_UNIT;
  K_LIST_COMMA;

  LIST;
  BAG;
  MAP;
}

K_UNIT : '.K' ;
K_ARROW : '~>' ;

K_LIST_UNIT : '.List{K}' ;
K_LIST_COMMA : ',,' ;

