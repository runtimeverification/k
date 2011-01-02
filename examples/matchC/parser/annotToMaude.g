tree grammar annotToMaude;

options {
  tokenVocab = annot;
  output = AST;
  ASTLabelType = CommonTree;
  //rewrite = true;
}

tokens {
  OP;
  CT;
}

root : node;

node_list
  : node+
  ;

node
  : ^(operator node_list)
  | constant
  | relation
  | container
  ;

assoc_id_node_list[String opString, String idString]
  : -> CT[idString]
  | DOWN assoc_node_list[opString] UP -> assoc_node_list
  ;

assoc_node_list[String opString]
  : node
    ( -> node
    | assoc_node_list[opString] -> ^(OP[opString] node assoc_node_list)
    )
  ;

relation
  : ^(relational_operator node_list)
    -> ^(OP["@_"] ^(relational_operator node_list))
  ;

container
  : MATH_OBJ_LIST! assoc_id_node_list["_`,_", ".List{MathObj++}"]
  | K_LIST! assoc_id_node_list["_`,`,_", ".List{K}"]
  | LIST! assoc_id_node_list["__", "(.).List"]
  | BAG! assoc_id_node_list["__", "(.).Bag"]
  | MAP! assoc_id_node_list["__", "(.).Map"]
;

relational_operator
  : LT     -> OP["_<Int_"]
  | LEQ    -> OP["_<=Int_"]
  | GT     -> OP["_>Int_"]
  | GEQ    -> OP["_>=Int_"]
;

operator
  : IDENTIFIER
  | unary_operator
  | binary_operator
  | SEQ             -> OP["`[_`]"]
  | MSET            -> OP["`{|_|`}"]
  | POINTSTO        -> OP["_|->_:_"]
  | HEAP_PATTERN    -> OP["_`(_`)`(_`)"]
  | CELL            -> OP["<_>_</_>"]
  | CONFIG          -> OP[""]
  | FIELD           -> OP["_._"]
  | MAP_ITEM
  | BAG_ITEM
  | LIST_ITEM
  | PRE
  | POST
  | ASSUME
  | ASSERT
  | INVARIANT
  ;

binary_operator
  : MAPSTO  -> OP["_|->_"]
  | K_ARROW -> OP["_~>_"]
  | DISJ    -> OP["_\\/_"]
  | CONJ    -> OP["_/\\_"]
  | EQ      -> OP["_===_"]
  | UNION   -> OP["_U_"]
  | APPEND  -> OP["_@_"]
  | ADD     -> OP["_+Int_"]
  | SUB     -> OP["_-Int_"]
  | MUL     -> OP["_*Int_"]
  | DIV     -> OP["_/Int_"]
  | REM     -> OP["_\%Int_"]
  ;

unary_operator
  : NEG      -> OP["~Int_"]
  | SIGN_POS -> OP["+Int_"]
  | SIGN_NEG -> OP["-Int_"]
  ;

constant
  : IDENTIFIER
  | DOT             -> CT["(.).K"]
  | K_UNIT          -> CT["(.).K"]
  | FORMULA_TRUE    -> CT["TrueFormula"]
  | FORMULA_FALSE   -> CT["FalseFormula"]
  | DECIMAL_LITERAL
  | OCTAL_LITERAL
  | HEX_LITERAL
  | STRING_LITERAL
  | LABEL
  | VERIFY
  | SKIP
  ;

