

module ISSUE146
  syntax K ::= Id | String | "test"
  syntax Id ::= "tRuE"
  define test => Id2String(tRuE)
end module
