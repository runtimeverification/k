

module SUDOKU-CONFIGURATION 

--- I wish I was able to use the same cell names below (lx -> x, etc.), but didn't work
  configuration <T>
                  <squares>
                    <square multiplicity="*">
                      <i>0</i>
                      <j>0</j>
                      <cells>
                        <cell multiplicity="*">
                          <x>0</x>
                          <y>0</y>
                          <v>.Bag</v>
                        </cell>
                      </cells>
                      <sc>.Map</sc>
                      <sdec multiplicity="*"> .Bag </sdec> 
                    </square>
                  </squares>
                  <lines>
                    <line multiplicity="*">
                      <lx>0</lx>
                      <lc>.Map</lc>
                      <ldec multiplicity="*">.Bag</ldec>
                    </line>
                  </lines>
                  <columns>
                    <column multiplicity="*">
                      <cy>0</cy>
                      <cc>.Map</cc>
                      <cdec multiplicity="*">.Bag</cdec>
                    </column>
                  </columns>
                </T>
end module

module SUDOKU-RULES imports SUDOKU-CONFIGURATION
--- naked single: square
  rule
       <cell_> <v>B:BagItem</v> <_/cell>
       <x>X:Nat</x> <y>Y:Nat</y> <v_>B=>.<_/v> (.Bag => <sdec>B</sdec>)
       <lx>X</lx>  (.Bag => <ldec>B</ldec>)
       <cy>Y</cy>  (.Bag => <cdec>B</cdec>)
  [structural]

--- naked single: line
  rule
       <square_> <x>X</x> <v>B</v> <_/square>
       <x>X</x> <y>Y</y> <v_>B=>.<_/v> (.Bag => <sdec>B</sdec>)
       <lx>X</lx>  (.Bag => <ldec>B</ldec>)
       <cy>Y</cy>  (.Bag => <cdec>B</cdec>)
  [structural]

--- naked single: column
  rule
       <square_> <y>Y</y> <v>B</v> <_/square>
       <x>X</x> <y>Y</y> <v_>B=>.<_/v> (.Bag => <sdec>B</sdec>)
       <lx>X</lx>  (.Bag => <ldec>B</ldec>)
       <cy>Y</cy>  (.Bag => <cdec>B</cdec>)
  [structural]


--- hidden single: square
  rule
       <x>X:Nat</x> <y>Y:Nat</y> <v>BagItem(V:Nat) (Bs:NeBag=>.)</v>
       <sc_>V|->1<_/sc>  (.Bag => <sdec>Bs</sdec>)
       <lx>X</lx>  (.Bag => <ldec>Bs</ldec>)
       <cy>Y</cy>  (.Bag => <cdec>Bs</cdec>)
  [structural]

--- hidden single: line
  rule
       <x>X:Nat</x> <y>Y:Nat</y> <v>BagItem(V) (Bs=>.)</v>
       (.Bag => <sdec>Bs</sdec>)
       <lx>X</lx> <lc_>V|->1<_/lc>  (.Bag => <ldec>Bs</ldec>)
       <cy>Y</cy>  (.Bag => <cdec>Bs</cdec>)
  [structural]

--- hidden single: column
  rule
       <x>X:Nat</x> <y>Y:Nat</y> <v>BagItem(V) (Bs=>.)</v>
       (.Bag => <sdec>Bs</sdec>)
       <lx>X</lx>  (.Bag => <ldec>Bs</ldec>)
       <cy>Y</cy> <cc_>V|->1<_/cc>  (.Bag => <cdec>Bs</cdec>)
  [structural]

--- nondeterministic choice (purposely only in 2-val cells; worked in all examples like that)
  rule [choose] :
       <x>X</x> <y>Y</y> <v>_:BagItem (B=>.)</v>  (.Bag => <sdec>B</sdec>)
       <lx>X</lx>  (.Bag => <ldec>B</ldec>)
       <cy>Y</cy>  (.Bag => <cdec>B</cdec>)


--- square decrement
  rule <sdec_>BagItem(V:Nat)=>.<_/sdec> <sc_>V |-> ((N:Nat)=>N -Int 1)<_/sc>   
  when N >Int 0 [structural]
  rule <sdec> .Bag </sdec> => . [structural]

--- line decrement
  rule <ldec_>BagItem(V:Nat)=>.<_/ldec> <lc_>V |-> ((N)=>N -Int 1)<_/lc>    
  when N >Int 0 [structural]
  rule <ldec> .Bag </ldec> => . [structural]

--- column decrement
  rule <cdec_>BagItem(V:Nat)=>.<_/cdec> <cc_>V |-> ((N)=>N -Int 1)<_/cc>
  when N >Int 0 [structural]
  rule <cdec> .Bag </cdec> => . [structural]
end module

module SUDOKU-INTERFACE imports SUDOKU-CONFIGURATION
  syntax Map ::= initMap
  macro initMap     = 1|->0  2|->0  3|->0  4|->0  5|->0  6|->0  7|->0  8|->0  9|->0

  macro BagItem(0) = Bag(1,,2,,3,,4,,5,,6,,7,,8,,9)

--- [_] transforms a sudoku board given as list into a K configuration
  syntax Bag ::= [ List{K} ]
               | mkConfig ( NeBag , List{K} , Nat , Bag , Bag , Bag )
               | addSquare ( NeBag , Nat , Nat , Nat , Nat , Bag )
               | addLine ( NeBag , Nat , Bag )
               | addColumn ( NeBag , Nat , Bag )
  syntax Map ::= inc ( Bag , Map )

  op headListK_ : List{K} -> K
  op tailListK_ : List{K} -> List{K}
  eq headListK(K:K,,Ks:List{K}) = K
  eq tailListK(K,,Ks) = Ks

  macro [V:Nat,,Vl:List{K}] = mkConfig(BagItem(V),Vl,0,.Bag,.Bag,.Bag)

  rule mkConfig(Bs:NeBag,Vl,N:Nat,Squares:Bag,Lines:Bag,Columns:Bag)
    => mkConfig(BagItem(headListK(Vl)),tailListK(Vl),(N +Int 1),
                addSquare(Bs, (N /Int 9) /Int 3, (N %Int 9) /Int 3, N /Int 9, N %Int 9, Squares),
                addLine(Bs, N /Int 9, Lines),
                addColumn(Bs, N %Int 9, Columns))
  [structural]

  rule mkConfig(_:NeBag,_,81,Squares,Lines,Columns)
    => <T_> <squares>Squares</squares> <lines>Lines</lines> <columns>Columns</columns> <_/T>
  [structural]

  rule addSquare(Bs, I:Nat, J:Nat, X:Nat, Y:Nat,
                 <square_> <i>I:Nat</i> <j>J:Nat</j> <sc>Map:Map</sc> <cells>Cells:Bag</cells> <_/square> Squares)
       => <square_> <i>I</i> <j>J</j> <sc>inc(Bs,Map)</sc>
                     <cells> Cells <cell> <x>X</x> <y>Y</y> <v>Bs</v> </cell> </cells> <_/square> Squares
  rule addSquare(Bs, I:Nat, J:Nat, X:Nat, Y:Nat,
                 <square_> <i>I':Nat</i> <j>J':Nat</j> <sc>Map:Map</sc> <cells>Cells:Bag</cells> <_/square> Squares)
       => <square_> <i>I'</i> <j>J'</j> <sc>Map</sc> <cells>Cells</cells> <_/square> addSquare(Bs,I,J,X,Y,Squares) 
  when I =/=Int I' orBool J =/=Int J'
  [structural]

  rule addSquare(Bs,I,J,X,Y,.Bag)
    => <square_> <i>I</i> <j>J</j> <sc>inc(Bs,initMap)</sc> <cells> <cell> <x>X</x> <y>Y</y> <v>Bs</v> </cell> </cells> <_/square>
  [structural]

  rule addLine(Bs,X:Nat, <line_> <lx>X:Nat</lx> <lc>Map</lc> <_/line> Lines)
    => <line_> <lx>X</lx> <lc>inc(Bs,Map)</lc> <_/line> Lines
  rule addLine(Bs,X:Nat, <line_> <lx>X':Nat</lx> <lc>Map</lc> <_/line> Lines)
       => <line_> <lx>X'</lx> <lc>Map</lc> <_/line> addLine(Bs,X,Lines) 
  when X =/=Int X'
  [structural]

  rule addLine(Bs,X,.Bag) => <line_> <lx>X</lx> <lc>inc(Bs,initMap)</lc> <_/line> [structural]

  rule addColumn(Bs,Y:Nat, <column_> <cy>Y:Nat</cy> <cc>Map</cc> <_/column> Columns)
    =>  <column_> <cy>Y</cy> <cc>inc(Bs,Map)</cc> <_/column> Columns
  rule addColumn(Bs,Y:Nat, <column_> <cy>Y':Nat</cy> <cc>Map</cc> <_/column> Columns)
    => <column_> <cy>Y'</cy> <cc>Map</cc> <_/column> addColumn(Bs,Y,Columns) 
  when Y =/=Int Y'
  [structural]
  rule addColumn(Bs,Y,.Bag) => <column_> <cy>Y</cy> <cc>inc(Bs,initMap)</cc> <_/column> [structural]

  rule inc((BagItem(V)=>.)_, V|->(N=>(N +Int 1))_) [structural]
  rule inc(.Bag,Map) => Map [structural]

--- Unfeasible configurations
  rule <T_> <cell_> <v> .Bag </v> <_/cell> <_/T> => .Bag [structural]
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
