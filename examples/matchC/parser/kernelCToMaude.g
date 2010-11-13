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
  | LIST
    ( -> CT[".List{KernelC}"]
    | DOWN list_node_list UP -> list_node_list
    )
  | SEQ
    ( -> CT[".KernelC"]
    | DOWN seq_node_list UP -> seq_node_list
    )
  | constant
  ;

node_list
  : node+
  ;

list_node_list
  : node
    ( -> node
    | list_node_list -> ^(OP["_`,`,`,_"] node list_node_list)
    )
  ;

seq_node_list
  : node
    ( -> node
    | seq_node_list -> ^(OP["_~~>_"] node seq_node_list)
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
  | FUN_DECL -> OP["__`(_`)"]
  | ANNOT_FUN_DECL -> OP["__`(_`)__"]
  | FUN_DEF -> OP["__`(_`)_"]
  | ANNOT_FUN_DEF -> OP["__`(_`)___"]
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
  | STRING_LITERAL
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
