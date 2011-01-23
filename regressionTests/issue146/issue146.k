in ../../k-prelude

kmod ISSUE146 is including K + PL-CONVERSION
  syntax K ::= Id | String | test
  syntax Id ::= tRuE
  rule test => Id2String(tRuE)
endkm
