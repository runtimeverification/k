

module IF 
  syntax K ::= if K then K else K   [strict(1)]
  syntax KResult ::= #Bool

  rule if true then E else _ => E:K
  rule if false then _ else E => E
end module
