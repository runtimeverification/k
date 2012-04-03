

module SUDOKU-CONFIGURATION imports K
  configuration <T> <cell multiplicity="*"> <x>0</x> <y>0</y> <v>.Bag</v> </cell> </T>
end module

module SUDOKU-RULES imports SUDOKU-CONFIGURATION
--- naked single
  rule <cell> <x>X1:Nat</x> <y>Y1:Nat</y> <v>B:BagItem</v> </cell>
       <cell> <x>X2:Nat</x> <y>Y2:Nat</y> <v>... B=>. ...</v> </cell>
    when (X1 ==Int X2 orBool Y1 ==Int Y2 orBool
       X1 /Int 3 ==Int X2 /Int 3 andBool Y1 /Int 3 ==Int Y2 /Int 3) [structural]

--- nondeterministic choice (purposely only in 2-val cells; worked in all examples like that)
  rule <cell>...  <v> B (_:BagItem => .) </v>  ...</cell> [transition]
end module

module SUDOKU-INTERFACE imports SUDOKU-CONFIGURATION
  macro BagItem(0) = Bag(1,,2,,3,,4,,5,,6,,7,,8,,9)
--- [_] transforms a sudoku board given as list into a K configuration
  syntax Bag ::= [ List{K} ] | mkCells ( Nat , List{K} )   --- transforms sudoku board into configuration
  macro [Vl:List{K}] = <T> mkCells(0,Vl) </T>
  macro mkCells(_:Nat,.List{K}) = .Bag
  macro mkCells(N:Nat,(V:K,,Vl:List{K}))
      = <cell> <x>N /Int 9</x> <y>N %Int 9</y> <v>BagItem(V)</v> </cell> mkCells(N +Int 1,Vl)

  rule <T>...  <cell>...  <v> .Bag </v>  ...</cell>  ...</T> => .Bag [structural]
end module

module SUDOKU imports SUDOKU-RULES + SUDOKU-INTERFACE
  syntax Bag ::= easy
  macro easy = [
0,,0,,4,, 7,,2,,0,, 9,,0,,0,,
0,,3,,9,, 0,,0,,8,, 0,,0,,5,,
0,,0,,1,, 5,,0,,6,, 0,,0,,4,,

0,,4,,0,, 0,,1,,0,, 5,,2,,0,,
0,,2,,8,, 0,,5,,0,, 1,,7,,0,,
0,,1,,6,, 0,,3,,0,, 0,,9,,0,,

4,,0,,0,, 9,,0,,1,, 3,,0,,0,,
1,,0,,0,, 3,,0,,0,, 8,,4,,0,,
0,,0,,7,, 0,,8,,5,, 6,,0,,0
]

  syntax Bag ::= escargot1
  macro escargot1 = [
8,,5,,0,, 0,,0,,2,, 4,,0,,0,,
7,,2,,0,, 0,,0,,0,, 0,,0,,9,,
0,,0,,4,, 0,,0,,0,, 0,,0,,0,,

0,,0,,0,, 1,,0,,7,, 0,,0,,2,,
3,,0,,5,, 0,,0,,0,, 9,,0,,0,,
0,,4,,0,, 0,,0,,0,, 0,,0,,0,,

0,,0,,0,, 0,,8,,0,, 0,,7,,0,,
0,,1,,7,, 0,,0,,0,, 0,,0,,0,,
0,,0,,0,, 0,,3,,6,, 0,,4,,0
]
end module
