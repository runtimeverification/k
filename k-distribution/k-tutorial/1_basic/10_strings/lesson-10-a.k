module LESSON-10-A
  imports STRING
  imports INT

  syntax String   ::= caps(String) [function]
                    | firstWord(String) [function]
                    | afterSentence(String) [function]
                    | ex(String) [function]

  syntax Int      ::= sentenceLen(haystack: String) [function]

  rule ex(S) => replaceAll(caps(S) +String ".", " .", ".")

  rule caps(S) => firstWord(S) +String " " +String
                  caps(afterSentence(S))
                  requires lengthString(S) >Int 0
  rule caps(_) => "" [owise]

  rule afterSentence(S) =>  substrString(S, findChar(S, ".", 0) +Int 2, lengthString(S))
                            requires findChar(S, ".", 0) +Int 2 <Int lengthString(S)
  rule afterSentence(_) => "" [owise]

  rule firstWord(S) => substrString(S, 0, findChar(S, " ", 0))
endmodule
