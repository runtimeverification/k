require "k-prelude.k"

interface CONSTANTS

  syntax #Bool ::= "true"
  				 | "false"

  syntax KLabel ::= "Int"   "(" #Int    ")"
                  | "Id"    "(" #String ")"
                  | "Float" "(" #Float  ")"
                  | "Bool"  "(" #Bool   ")"

endinterface

interface #PL-BOOL
  syntax #Bool ::= K "=/=Bool" K            [cons("DzBool1NEqBuiltin")] // these sorts should be Universal, not K
                 | K "==Bool"  K            [cons("DzBool1EqBuiltin")]
                 | "notBool" #Bool 	        [cons("DzBool1NotBoolBuiltin")]
                 > #Bool "andBool" #Bool    [left, cons("DzBool1AndBuiltin")]
                 > #Bool "orBool"  #Bool    [left, cons("DzBool1OrBuiltin")]
endinterface

interface #PL-INT
  including #PL-BOOL
  // This is an interface to the Int built-in
  syntax #Int ::= "-Int" #Int	  [cons("DzInt1IntUMinusBuiltin")]
               > left:
                 #Int "*Int" #Int [left, cons("DzInt1IntMulBuiltin")]
               | #Int "/Int" #Int [left, cons("DzInt1IntDivBuiltin")]
               | #Int "%Int" #Int [left, cons("DzInt1IntModBuiltin")]
               > left:
                 #Int "+Int" #Int [left, cons("DzInt1IntPlusBuiltin")]
               | #Int "-Int" #Int [left, cons("DzInt1IntMinusBuiltin")]

  syntax #Bool ::= non-assoc:
                  #Int "<Int"  #Int [cons("DzBool1IntLTBuiltin")]
                | #Int "<=Int" #Int [cons("DzBool1IntLTEBuiltin")]
                | #Int ">Int"  #Int [cons("DzBool1IntGTBuiltin")]
                | #Int ">=Int" #Int [cons("DzBool1IntGTEBuiltin")] 

endinterface

interface #PL-BUILTINS
  including #PL-BOOL + #PL-NAT + #PL-INT
endinterface

interface #FLOAT
endinterface

interface #STRING
  syntax #String ::= #String "+String" #String [left, cons("DzString1StrPlusBuiltin")]

endinterface

interface #CONVERSION
endinterface



// from socket.k
interface #CONFIGURATION
endinterface

interface #SOCKET
endinterface
