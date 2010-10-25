tree grammar kernelCToMaude;

options {
  tokenVocab = kernelC;
  output = AST;
  ASTLabelType = CommonTree;
  //rewrite = true;
}

tokens {
  OP;
  CT;
}

root : node;

node
  : ^(operator node_list)
  | KLIST
    ( -> OP[".List{KernelC}"]
    | DOWN klist_node_list UP -> klist_node_list
    )
  | KARROW
    ( -> OP["(.).K"]
    | DOWN karrow_node_list UP -> karrow_node_list
    )
  | constant
  ;

node_list
  : node+
  ;

klist_node_list
  : node
    ( -> node
    | klist_node_list -> ^(OP["_`,`,`,_"] node klist_node_list)
    )
  ;

karrow_node_list
  : node
    ( -> node
    | karrow_node_list -> ^(OP["_~>_"] node karrow_node_list)
    )
  ;

operator
  : unary_operator
  | binary_operator
  | '?' -> OP["_?_:_"]
  | CAST -> OP["`(_`)_"]
  | CALL -> OP["_`(_`)"]
  | INDEX -> OP["_`[_`]"]
  | 'sizeof' -> OP["sizeof_"]
  | ';' -> OP["_;"]
  | IF -> OP["if`(_`)_else_"]
  | WHILE -> OP["while`(_`)_"]
  | RETURN -> OP["return_"]
  | BLOCK -> OP["block_"]
  | VAR_DECL -> OP["__;"]
  | STRUCT_DECL -> OP["struct_`{_`};"]
  | FUN_DECL -> OP["__`(_`)__"]
  | FUN_DEF -> OP["__`(_`)___"]
  | STRUCT -> OP["struct_"]
  | PTR -> OP["_*"]
  | PARAM -> OP["__;"]
  | TRANS_UNIT -> OP["translationUnit_"]
  ;

binary_operator
  : '='   -> OP["_=_"]
  | '*='  -> OP["_*=_"]
  | '/='  -> OP["_/=_"]
  | '%='  -> OP["_\%=_"]
  | '+='  -> OP["_+=_"]
  | '-='  -> OP["_-=_"]
  | '<<=' -> OP["_<<=_"]
  | '>>=' -> OP["_>>=_"]
  | '&='  -> OP["_&=_"]
  | '^='  -> OP["_^=_"]
  | '|='  -> OP["_|=_"]
  | '||'  -> OP["_||_"]
  | '&&'  -> OP["_&&_"]
  | '|'   -> OP["_|_"]
  | '^'   -> OP["_^_"]
  | '&'   -> OP["_&_"]
  | '=='  -> OP["_==_"]
  | '!='  -> OP["_!=_"]
  | '<'   -> OP["_<_"]
  | '>'   -> OP["_>_"]
  | '<='  -> OP["_<=_"]
  | '>='  -> OP["_>=_"]
  | '<<'  -> OP["_<<_"]
  | '>>'  -> OP["_>>_"]
  | '+'   -> OP["_+_"]
  | '-'   -> OP["_-_"]
  | '*'   -> OP["_*_"]
  | '/'   -> OP["_/_"]
  | '\%'   -> OP["_\%_"]
  | '.'   -> OP["_._"]
  | '->'  -> OP["_->_"]
  ;

unary_operator
  : REF      -> OP["&"]
  | DEREF    -> OP["*"]
  | SIGN_POS -> OP["+"]
  | SIGN_NEG -> OP["-"]
  | '~'      -> OP["~"]
  | '!'      -> OP["!"]
  | '++'     -> OP["++"]
  | '--'     -> OP["--"]
  ;

constant
  : IDENTIFIER
  | arithmetic_constant -> ^(OP["tv"] CT["int"] arithmetic_constant)
  | VOID_EXP -> ^(OP["tv"] CT["void"] CT["unit"])
  | NOP -> CT["nop"]
  | 'void'
  | 'int'
  | ANNOTATION
  ;

arithmetic_constant
  : DECIMAL_LITERAL
  | OCTAL_LITERAL
  | HEX_LITERAL
  ;
