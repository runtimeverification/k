module A
  syntax One ::= one
  syntax Two ::= two
  syntax Three ::= three
  syntax Two ::= One
  syntax Ones ::= List{One,","}
// generate all lists for Ones
end module

module B
  imports A
  syntax Twos ::= List{Two,","}
  syntax Twoos ::= List{Two,""}
// generate all list for Twos and Twoos
// subsort the lists for Ones to those for Twos (syntax Two ::= One in module A)
end module

module C
  imports A
  syntax Three ::= One
  syntax Threes ::= List{Three,","}
// generate all lists for Threes
// subsort the lists for Ones to those for Threes 
end module

module D
  imports B + C 
  syntax Four ::= Two | Three
  syntax Fours ::= List{Four,","}
// generate all lists for Fours
// subsort the lists for Twos and Threes to those for Fours 
end module
