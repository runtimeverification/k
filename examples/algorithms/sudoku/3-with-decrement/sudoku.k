

module SUDOKU-CONFIGURATION
  syntax K ::= Nat
  syntax MapItem ::= Nat |-> BagItem

--- I wish I was able to use the same cell names below (lx -> x, etc.), but didn't work
  configuration <T>
                  <cells>
                    <cell multiplicity="*">
                      <x>0</x>
                      <y>0</y>
                      <i>0</i>
                      <j>0</j>
                      <v>.Bag</v>
                    </cell>
                  </cells>
                  <data-structures>
                    <squares> <square multiplicity="*"> <si>0</si> <sj>0</sj> <sc>.Map</sc> </square> </squares>
                    <lines>   <line multiplicity="*">   <lx>0</lx> <lc>.Map</lc> </line>   </lines>
                    <columns> <column multiplicity="*"> <cy>0</cy> <cc>.Map</cc> </column> </columns>
                    <decrement multiplicity="*"> <di>0</di> <dj>0</dj> <dx>0</dx> <dy>0</dy> <dv>.Bag</dv> </decrement>
                  </data-structures>
                </T>
end module

module SUDOKU-RULES is including SUDOKU-CONFIGURATION
--- naked single
  rule
       <cell_> <x>X1:Nat</x> <y>Y1:Nat</y> <v>B:BagItem</v> <_/cell>
       <cell>  <x>X2:Nat</x> <y>Y2:Nat</y> <i>I:Nat</i> <j>J:Nat</j> <v_>B=>.<_/v> </cell>
       (.Bag => <decrement> <di>I</di> <dj>J</dj> <dx>X2</dx> <dy>Y2</dy> <dv>B</dv> </decrement>)
    when (X1 ==Int X2 orBool Y1 ==Int Y2 orBool
       X1 /Int 3 ==Int X2 /Int 3 andBool Y1 /Int 3 ==Int Y2 /Int 3)
  [structural]

--- hidden single: square
  rule [hidden-square] :
       <cell> <i>I</i> <j>J</j> <x>X:Nat</x> <y>Y:Nat</y> <v>BagItem(V:Nat) (Bs:NeBag=>.)</v> </cell>
       <square> <si>I</si> <sj>J</sj> <sc_>V|->1<_/sc> </square>
       (.Bag => <decrement> <di>I</di> <dj>J</dj> <dx>X</dx> <dy>Y</dy> <dv>Bs</dv> </decrement>)
  [structural]

--- hidden single: line
  rule [hidden-line] :
       <cell> <i>I</i> <j>J</j> <x>X</x> <y>Y</y> <v>BagItem(V) (Bs=>.)</v> </cell>
       <line>   <lx>X</lx> <lc_>V|->1<_/lc> </line>
       (.Bag => <decrement> <di>I</di> <dj>J</dj> <dx>X</dx> <dy>Y</dy> <dv>Bs</dv> </decrement>)
  [structural]

--- hidden single: column
  rule [hidden-column] :
       <cell> <i>I</i> <j>J</j> <x>X</x> <y>Y</y> <v>BagItem(V) (Bs=>.)</v> </cell>
       <column> <cy>Y</cy> <cc_>V|->1<_/cc> </column>
       (.Bag => <decrement> <di>I</di> <dj>J</dj> <dx>X</dx> <dy>Y</dy> <dv>Bs</dv> </decrement>)
  [structural]

--- decrement: non-empty
  rule
       <decrement> <di>I</di> <dj>J</dj> <dx>X</dx> <dy>Y</dy> <dv_>BagItem(V)=>.<_/dv> </decrement>
       <square> <si>I</si> <sj>J</sj> <sc_>V |-> ((Ns:Nat)=>Ns -Int 1)<_/sc> </square>
       <line> <lx>X</lx> <lc_>V |-> ((Nl:Nat)=>Nl -Int 1)<_/lc> </line>
       <column> <cy>Y</cy> <cc_>V |-> ((Nc:Nat)=>Nc -Int 1)<_/cc> </column>
   when Ns >Int 0 andBool Nl >Int 0 andBool Nc >Int 0
  [structural]

--- decrement: empty
  rule
       <decrement_> <dv>.Bag</dv> <_/decrement> => .
  [structural]

--- nondeterministic choice (purposely only in 2-val cells; worked in all examples like that)
  rule [choose] :
       <cell> <i>I</i> <j>J</j> <x>X</x> <y>Y</y> <v>BagItem(V) (B=>.)</v> </cell>
       (.Bag => <decrement> <di>I</di> <dj>J</dj> <dx>X</dx> <dy>Y</dy> <dv>B</dv> </decrement>)
  [transition]
end module

module SUDOKU-INTERFACE is including SUDOKU-CONFIGURATION
  syntax Map ::= initMap
  macro initMap     = 1|->0  2|->0  3|->0  4|->0  5|->0  6|->0  7|->0  8|->0  9|->0

  macro BagItem(0) = Bag(1,,2,,3,,4,,5,,6,,7,,8,,9)

--- [_] transforms a sudoku board given as list into a K configuration
  syntax Bag ::= [ List{K} ]
               | mkConfig ( NeBag , List{K} , Nat , Bag , Bag , Bag , Bag )
               | addSquare ( NeBag , Nat , Nat , Bag )
               | addLine ( NeBag , Nat , Bag )
               | addColumn ( NeBag , Nat , Bag )
  syntax Map ::= inc ( Bag , Map )

  op headListK_ : List{K} -> K
  op tailListK_ : List{K} -> List{K}
  eq headListK(K:K,,Ks:List{K}) = K
  eq tailListK(K,,Ks) = Ks

  macro [V:Nat,,Vl:List{K}] = mkConfig(BagItem(V),Vl,0,.Bag,.Bag,.Bag,.Bag)

  rule mkConfig(Bs:NeBag,Vl,N:Nat,Squares:Bag,Lines:Bag,Columns:Bag,Cells:Bag)
    => mkConfig(BagItem(headListK(Vl)),tailListK(Vl),(N +Int 1),
                addSquare(Bs, (N /Int 9) /Int 3, (N %Int 9) /Int 3, Squares),
                addLine(Bs, N /Int 9, Lines),
                addColumn(Bs, N %Int 9, Columns),
                Cells <cell> <i>(N /Int 9) /Int 3</i> <j>(N %Int 9) /Int 3</j> <x>N /Int 9</x> <y>N %Int 9</y> <v>Bs</v> </cell>)
       [structural]
  rule mkConfig(_:NeBag,_,81,Squares,Lines,Columns,Cells)
    => <T_> <cells>Cells</cells> <squares>Squares</squares> <lines>Lines</lines> <columns>Columns</columns> <_/T> [structural]

  rule addSquare(Bs,I:Nat,J:Nat, <square> <si>I:Nat</si> <sj>J:Nat</sj> <sc>Map:Map</sc> </square> Squares)
       => <square> <si>I</si> <sj>J</sj> <sc>inc(Bs,Map)</sc> </square> Squares
  rule addSquare(Bs,I:Nat,J:Nat, <square> <si>I':Nat</si> <sj>J':Nat</sj> <sc>Map:Map</sc> </square> Squares)
    => <square> <si>I'</si> <sj>J'</sj> <sc>Map</sc> </square> addSquare(Bs,I,J,Squares) 
  when I =/=Int I' orBool J =/=Int J' [structural]
  rule addSquare(Bs,I,J,.Bag) => <square> <si>I</si> <sj>J</sj> <sc>inc(Bs,initMap)</sc> </square> [structural]

  rule addLine(Bs,X:Nat, <line> <lx>X:Nat</lx> <lc>Map</lc> </line> Lines)
    => <line> <lx>X</lx> <lc>inc(Bs,Map)</lc> </line> Lines
  rule addLine(Bs,X:Nat, <line> <lx>X':Nat</lx> <lc>Map</lc> </line> Lines)
       => <line> <lx>X'</lx> <lc>Map</lc> </line> addLine(Bs,X,Lines)
  when  X =/=Int X'
 [structural]
  rule addLine(Bs,X,.Bag) => <line> <lx>X</lx> <lc>inc(Bs,initMap)</lc> </line> [structural]

  rule addColumn(Bs,Y:Nat, <column> <cy>Y:Nat</cy> <cc>Map</cc> </column> Columns)
    =>  <column> <cy>Y</cy> <cc>inc(Bs,Map)</cc> </column> Columns
  rule addColumn(Bs,Y:Nat, <column> <cy>Y':Nat</cy> <cc>Map</cc> </column> Columns)
    =>  <column> <cy>Y'</cy> <cc>Map</cc> </column> addColumn(Bs,Y,Columns) 
   when Y =/=Int Y'
[structural]
  rule addColumn(Bs,Y,.Bag) => <column> <cy>Y</cy> <cc>inc(Bs,initMap)</cc> </column> [structural]

  rule inc((BagItem(V)=>.)_, V|->(N=>(N +Int 1))_) [structural]
  rule inc(.Bag,Map) => Map [structural]

--- Unfeasible configurations
  rule <T_> <cell_> <v> .Bag </v> <_/cell> <_/T> => .Bag [structural]
end module

module SUDOKU is including SUDOKU-RULES + SUDOKU-INTERFACE
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

  syntax Bag ::= escargot2
  macro escargot2 = [
1,,0,,0,, 0,,0,,7,, 0,,9,,0,,
0,,3,,0,, 0,,2,,0,, 0,,0,,8,,
0,,0,,9,, 6,,0,,0,, 5,,0,,0,,

0,,0,,5,, 3,,0,,0,, 9,,0,,0,,
0,,1,,0,, 0,,8,,0,, 0,,0,,2,,
6,,0,,0,, 0,,0,,4,, 0,,0,,0,,

3,,0,,0,, 0,,0,,0,, 0,,1,,0,,
0,,4,,0,, 0,,0,,0,, 0,,0,,7,,
0,,0,,7,, 0,,0,,0,, 3,,0,,0
]
end module
