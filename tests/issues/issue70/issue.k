module ISSUE

syntax K ::= "toFloat" "(" String ")"

rule toFloat(Str:String) => #if (lastChar(Str) ==String "F")
                              #then Str
                              #else String2Float(Str)
                            #fi

syntax K ::= "lastChar" "(" String ")"                                  [function]
rule lastChar(Str:String) => substrString(Str, lengthString(Str) -Int 1, lengthString(Str))

endmodule
