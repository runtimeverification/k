in ../../../k-prelude

kmod SUDOKU-CONFIGURATION is including K
  syntax K ::= Nat
  syntax MapItem ::= Nat |-> BagItem

--- I wish I was able to use the same cell names below (lx -> x, etc.), but didn't work
  configuration <T>
                  <cells>
                    <cell*>
                      <x>0</x>
                      <y>0</y>
                      <i>0</i>
                      <j>0</j>
                      <v>.Bag</v>
                    </cell*>
                  </cells>
                  <data-structures>
                    <squares> <square*> <si>0</si> <sj>0</sj> <sc>.Map</sc> </square*> </squares>
                    <lines>   <line*>   <lx>0</lx> <lc>.Map</lc> </line*>   </lines>
                    <columns> <column*> <cy>0</cy> <cc>.Map</cc> </column*> </columns>
                  </data-structures>
                </T>
endkm

kmod SUDOKU-RULES is including SUDOKU-CONFIGURATION
--- naked single: square

  rule
       <cell_> <x>X1:Nat</x> <y>Y1:Nat</y> <v>BagItem(V:Nat)</v> <_/cell>
       <cell>  <x>X2:Nat</x> <y>Y2:Nat</y> <i>I:Nat</i> <j>J:Nat</j> <v_>BagItem(V)=>.<_/v> </cell>
       <square> <si>I</si> <sj>J</sj> <sc_>V |-> (sNat(Ns:Nat)=>Ns)<_/sc> </square>
       <line> <lx>X2</lx> <lc_>V |-> (sNat(Nl:Nat)=>Nl)<_/lc> </line>
       <column> <cy>Y2</cy> <cc_>V |-> (sNat(Nc:Nat)=>Nc)<_/cc> </column>
    if (X1 ==Bool X2 orBool Y1 ==Bool Y2 orBool
       X1 /Nat 3 ==Bool X2 /Nat 3 andBool Y1 /Nat 3 ==Bool Y2 /Nat 3) [structural]

--- the rule above can be replaced by the one below, but then kompilation becomes very slow
***(
  rule
       <cell_> <x>X1:Nat</x> <y>Y1:Nat</y> <v>BagItem(V:Nat)</v> <_/cell>
               <x>X2:Nat</x> <y>Y2:Nat</y> <i>I:Nat</i> <j>J:Nat</j> <v_>BagItem(V)=>.<_/v>
               <si>I</si> <sj>J</sj> <sc_>V |-> (sNat(Ns:Nat)=>Ns)<_/sc>
               <lx>X2</lx> <lc_>V |-> (sNat(Nl:Nat)=>Nl)<_/lc>
               <cy>Y2</cy> <cc_>V |-> (sNat(Nc:Nat)=>Nc)<_/cc>
    if (X1 ==Bool X2 orBool Y1 ==Bool Y2 orBool
       X1 /Nat 3 ==Bool X2 /Nat 3 andBool Y1 /Nat 3 ==Bool Y2 /Nat 3) [structural]
***)

--- hidden single: square
  rule [hidden-square] :
       <cell> <i>I</i> <j>J</j> <x>X:Nat</x> <y>Y:Nat</y> <v_>BagItem(V) (BagItem(V':Nat)=>.)<_/v> </cell>
       <square> <si>I</si> <sj>J</sj> <sc_>V|->1 V'|->(sNat(Ns)=>Ns)<_/sc> </square>
       <line>   <lx>X</lx> <lc_>V' |-> (sNat(Nl:Nat)=>Nl)<_/lc> </line>
       <column> <cy>Y</cy> <cc_>V' |-> (sNat(Nc:Nat)=>Nc)<_/cc> </column> [structural]

--- hidden single: line
  rule [hidden-line] :
       <cell> <i>I</i> <j>J</j> <x>X</x> <y>Y</y> <v_>BagItem(V) (BagItem(V')=>.)<_/v> </cell>
       <square> <si>I</si> <sj>J</sj> <sc_>V'|->(sNat(Ns)=>Ns)<_/sc> </square>
       <line>   <lx>X</lx> <lc_>V|->1 V' |-> (sNat(Nl:Nat)=>Nl)<_/lc> </line>
       <column> <cy>Y</cy> <cc_>V' |-> (sNat(Nc:Nat)=>Nc)<_/cc> </column> [structural]

--- hidden single: column
  rule [hidden-column] :
       <cell> <i>I</i> <j>J</j> <x>X</x> <y>Y</y> <v_>BagItem(V) (BagItem(V')=>.)<_/v> </cell>
       <square> <si>I</si> <sj>J</sj> <sc_>V'|->(sNat(Ns)=>Ns)<_/sc> </square>
       <line>   <lx>X</lx> <lc_>V' |-> (sNat(Nl:Nat)=>Nl)<_/lc> </line>
       <column> <cy>Y</cy> <cc_>V|->1 V' |-> (sNat(Nc:Nat)=>Nc)<_/cc> </column> [structural]

--- nondeterministic choice (purposely only in 2-val cells; worked in all examples like that)
  rule [choose] :
       <cell> <i>I</i> <j>J</j> <x>X</x> <y>Y</y> <v>BagItem(V) (BagItem(V')=>.)</v> </cell>
       <square> <si>I</si> <sj>J</sj> <sc_>V'|->(sNat(Ns)=>Ns)<_/sc> </square>
       <line>   <lx>X</lx> <lc_>V' |-> (sNat(Nl)=>Nl)<_/lc> </line>
       <column> <cy>Y</cy> <cc_>V' |-> (sNat(Nc)=>Nc)<_/cc> </column>
endkm

kmod SUDOKU-INTERFACE is including SUDOKU-CONFIGURATION
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
    => mkConfig(BagItem(headListK(Vl)),tailListK(Vl),sNat(N),
                addSquare(Bs, (N /Nat 9) /Nat 3, (N %Nat 9) /Nat 3, Squares),
                addLine(Bs, N /Nat 9, Lines),
                addColumn(Bs, N %Nat 9, Columns),
                Cells <cell> <i>(N /Nat 9) /Nat 3</i> <j>(N %Nat 9) /Nat 3</j> <x>N /Nat 9</x> <y>N %Nat 9</y> <v>Bs</v> </cell>)
       [structural]
  rule mkConfig(_,_,81,Squares,Lines,Columns,Cells)
    => <T_> <cells>Cells</cells> <squares>Squares</squares> <lines>Lines</lines> <columns>Columns</columns> <_/T> [structural]

  rule addSquare(Bs,I:Nat,J:Nat, <square> <si>I':Nat</si> <sj>J':Nat</sj> <sc>Map:Map</sc> </square> Squares)
    => if I ==Bool I' andBool J ==Bool J'
       then <square> <si>I</si> <sj>J</sj> <sc>inc(Bs,Map)</sc> </square> Squares
       else <square> <si>I'</si> <sj>J'</sj> <sc>Map</sc> </square> addSquare(Bs,I,J,Squares) fi [structural]
  rule addSquare(Bs,I,J,.Bag) => <square> <si>I</si> <sj>J</sj> <sc>inc(Bs,initMap)</sc> </square> [structural]

  rule addLine(Bs,X:Nat, <line> <lx>X':Nat</lx> <lc>Map</lc> </line> Lines)
    => if X ==Bool X' then <line> <lx>X</lx> <lc>inc(Bs,Map)</lc> </line> Lines
       else <line> <lx>X'</lx> <lc>Map</lc> </line> addLine(Bs,X,Lines) fi [structural]
  rule addLine(Bs,X,.Bag) => <line> <lx>X</lx> <lc>inc(Bs,initMap)</lc> </line> [structural]

  rule addColumn(Bs,Y:Nat, <column> <cy>Y':Nat</cy> <cc>Map</cc> </column> Columns)
    => if Y ==Bool Y' then <column> <cy>Y</cy> <cc>inc(Bs,Map)</cc> </column> Columns
       else <column> <cy>Y'</cy> <cc>Map</cc> </column> addColumn(Bs,Y,Columns) fi [structural]
  rule addColumn(Bs,Y,.Bag) => <column> <cy>Y</cy> <cc>inc(Bs,initMap)</cc> </column> [structural]

  rule inc((BagItem(V)=>.)_, V|->(N=>sNat(N))_) [structural]
  rule inc(.Bag,Map) => Map [structural]

--- Unfeasible configurations
  rule <T_> <cell_> <v> .Bag </v> <_/cell> <_/T> => .Bag [structural]
endkm

kmod SUDOKU is including SUDOKU-RULES + SUDOKU-INTERFACE
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
endkm
