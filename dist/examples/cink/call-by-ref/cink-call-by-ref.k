//require "../basic/cink-basic-syntax.k"
require "../arrays/cink-arrays.k"

module CINK-CALL-BY-REF-SYNTAX
  syntax Exp ::= "&" Exp [ampersand]
  syntax priorities  ampersand > assign read write greatthan lessequal
endmodule

module CINK-CALL-BY-REF-SEMANTICS

  imports CINK-BASIC-SYNTAX
  imports CINK-CALL-BY-REF-SYNTAX
  imports CINK-BASIC-SEMANTICS
  imports CINK-L-R-VALUES-SEMANTICS

  context evaluate((HOLE => lvalue(HOLE)), _:Exps) to _:Vals
          following  (T:Type (& X:Id)::Exp, _:Decls);


  /*@ For call-by-reference, the location pointed to by the lvalue is directly
      bound to the formal parameter:
  */
  rule <k> bind((L:LVal, Vs:Vals) => Vs)
           to((T:Type & X:Id, Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env> 
  

endmodule
