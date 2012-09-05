module K-PARSER
  syntax K ::= "parseSKExp" "(" String ")"
  syntax K ::= "parseSKExps" "(" String "," K ")"

  rule parseSKExp(S:String) 
    => parseSKExp(substrString(S,0,1), ltrimSpacesString(substrString(S,1, lengthString(S))))

  rule parseSKExp("(", S:String)
    => parseSKExpLabel(substrString(S, 0, 1), S:String)

  rule parseSKExpLabel("(", S:String)
    => parseSKExpInjectedLabel(ltrimSpacesString(substrString(S,1, lengthString(S))))
  rule parseSKExpLabel(S1:String, S2:String)
    => parseSKExpRealLabel(S2,findString(S2, " ", 0))
    when S1 =/=String "("

  rule parseSKExpRealLabel(S:String, I:Int)
    => parseSKExps(ltrimSpaces(substrString(S, I +Int 1, lengthString(S))), String2KLabel(substrString(S, 0, I -Int 1))(.List{K}))

  rule parseSKExps(S:String, K:K) 
    => parseSKExps(substrString(S,0,1), S, K)

  rule parseSKExps(")", S, K) => pair(K, ltrimSpaces(substrString(S, 1, lengthString(S))))
  rule parseSKExps(S1:String, S2:String, K:K)
    => parseSExp(S2) ~> parseSKExps(HOLE, K)
    when S1 =/=String ")"

  rule (pair(K:K, S:String) => .K) ~> parseSKExps(HOLE => S, L:KLabel(_,,(.List{K} => K)))

  rule parseSKExpInjectedLabel(S:String)
    => parseSKExpInjectedLabelType(S, findString(S, " ", 0))
  rule parseSExpInjectedLabelType(S:String, I:Int)
    => parseSExpInjectedLabel(ltrimSpacesString(substrString(S,0, I -Int 1)), ltrimSpacesString(substrString(S, I +Int 1, lengthString(S))))
  rule parseSExpInjectedLabel(S1:String, S2:String)
    => parseSExpInjectedLabel(S1, S2, findString(S2, ")", 0))
    when S1 =/=String "String"

  rule parseSKExpInjectedLabel(S1:String, S2:String, I:Int)
    => parseSKExps(ltrimSpacesString(substrString(S2, I +Int 1, lengthString(S2))), #convertToken(S1, lTrimSpacesString(substrString(S2, 0, I -Int 1))))

  rule parseSKExpInjectedLabel("String", S:String)
    => parseSKExpInjectedString(S, findString(S,"\"",0))

  rule parseSKExpInjectedString(S:String, I:Int)
    => parseSKExpInjectedString(S, I, findString(S,"\"",I +Int 1))
  rule parseSKExpInjectedString(S:String, I1:Int, I2:Int)
    =>  parseSKExpInjectedString(S, I1, I2, substrString(S,I2 -Int 1, 1))

  rule parseSKExpInjectedString(S:String, I1:Int, I2:Int, "\\")
    => parseSKExpInjectedString(S, I1, findString(S,"\"",I2 +Int 1))
  rule parseSKExpInjectedString(S1:String, I1:Int, I2:Int, S2:String)
    => parseSKExps(ltrimSpacesString(substrString(S1, findString(S1, ")", I2 +Int 1), lengthString(S2))), #convertToken(S1, lTrimSpacesString(substrString(S1, I1 +Int 1, I2 -Int 1))))
    when S2 =/=String "\\"


endmodule
