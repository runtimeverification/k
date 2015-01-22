// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST

     syntax Bits ::= piece(Bits, Int)
     syntax Bits ::= Bits "bit::" Bits
     syntax Bits ::= Int

     syntax Trap ::= "trap"
     syntax Unknown ::= "unknown"
     syntax Bits ::= Trap
     syntax Bits ::= Unknown

     syntax CSize ::= Int
     syntax CValue ::= CSize

     syntax CValue ::= Bits | Float
     syntax Int ::= "cfg:bitsPerByte" [function]

     syntax Bits ::= dataList(List) | env(String)

     configuration <k> $PGM:K </k><env> .Map </env>

     rule cfg:bitsPerByte => 8

     syntax Bits ::= bitRange(Bits, Int, Int)

     rule piece(bitRange(N:Bits, SuccTo:Int, To':Int), Len:Int)
               bit:: piece(bitRange(N, From:Int, To:Int), Len':Int)
          => piece(bitRange(N, From, To'), Len +Int Len')
          requires (Len +Int Len' <=Int cfg:bitsPerByte)
               andBool (SuccTo ==Int To +Int 1)
          [structural, anywhere]

     rule piece(N:Bits bit:: N':Bits, Len:Int) bit:: piece(N'':Bits, Len':Int)
          => piece((N bit:: N') bit:: piece(N'', Len'), Len +Int Len')
          [structural, anywhere]

     rule piece(N'':Bits, Len':Int) bit:: piece(N:Bits bit:: N':Bits, Len:Int)
          => piece((piece(N'', Len') bit:: N) bit:: N', Len +Int Len')
          [structural, anywhere]

     rule piece(0, 0) bit:: N:Bits => N
          [structural, anywhere]

     rule piece(piece(N:Bits, Len:Int), Len:Int) => piece(N, Len)
          [structural, anywhere]

     rule bitRange(N:Bits bit:: piece(_, Len:Int), Pos:Int, Pos)
          => bitRange(N, absInt(Pos -Int Len), absInt(Pos -Int Len))
          requires (Pos >Int 0) andBool (Pos -Int Len >=Int 0)
          [structural, anywhere]

     rule bitRange(_ bit:: piece(N:Bits, 1), 0, 0) => piece(N, 1)
          [structural, anywhere]

     rule bitRange(piece(N:Bits, 1), 0, 0) => piece(N, 1)
          [structural, anywhere]

     rule bitRange(piece(bitRange(N:Bits, Start:Int, End:Int), Len:Int), 0, 0)
          => bitRange(piece(bitRange(N, Start, Start), 1), 0, 0)
          requires Start +Int Len ==Int End +Int 1
          [structural, anywhere]

     rule bitRange(N:Int, Pos:Int, Pos:Int) => 1 &Int (N >>Int Pos)
          requires N >=Int 0
          [structural, anywhere]

     rule bitRange(piece(N:Int, 1), Pos:Int, Pos:Int) => 1 &Int (N >>Int Pos)
          requires N >=Int 0
          [structural, anywhere]

     rule bitRange(N:Bits, 0, To:Int) => N
          requires To +Int 1 ==Int cfg:bitsPerByte
          [structural, anywhere]

     rule bitRange(_ bit:: piece(N:Bits, Len:Int), Start:Int, End:Int)
          => bitRange(piece(N, Len), Start, End)
          requires End +Int 1 <=Int Len
          [structural, anywhere]

     rule bitRange(piece(N:Bits, SuccEnd:Int), 0, End:Int)
          => piece(N, End +Int 1)
          requires SuccEnd ==Int End +Int 1
          [structural, anywhere]

     rule bitRange(_ bit:: piece(N:Bits, SuccEnd:Int), 0, End:Int)
          => piece(N, End +Int 1)
          requires SuccEnd ==Int End +Int 1
          [structural, anywhere]

     rule bitRange(piece(N:Int, _), Pos:Int, Pos:Int)
          => (N >>Int Pos) &Int 1
          requires N >=Int 0
          [structural, anywhere]

     rule piece(N:Int, Len:Int) bit:: piece(N':Int, Len':Int)
          => piece((N <<Int Len') |Int N', Len +Int Len')
          [structural, anywhere]

     rule <k>(env(S:String) ~> B:Bits) => . ...</k>
       <env>... (.Map => S |-> B) ...</env>

     rule dataList(ListItem(A:Bits) ListItem(B:Bits) L:List) => dataList(ListItem(A bit:: B)) [structural,anywhere]

     syntax KItem ::= "start" | "start1" | "start2" | "start3"
        | "start4" | "start5" | "start6"
        | "start7" | "start8" | "start9"
        | "start10" | "start11"

     rule start => env("a") ~> (piece(0,0) bit::
            piece(1,1)) bit:: piece(0 bit:: piece(1,1),1)

     rule start1 => env("a") ~> piece(0,0) bit::
            (piece(1,1) bit:: piece(0 bit:: piece(1,1),1))
            ~> env("b") ~> (piece(0,0) bit:: piece(1,1))
            bit:: piece(0 bit:: piece(1,1),1)

     rule start2 => env("a") ~> piece(1,0) bit:: (piece(0,0)
            bit:: piece(0 bit:: piece(1,1),1)) ~>
            env("c") ~> (piece(0,0) bit:: piece(1,1))
             bit:: piece(0 bit:: piece(1,1),1)

     rule start3 => env("a") ~> bitRange(piece(0,0),0,7) bit:: piece(1,1)

     rule start4 => env("a") ~> bitRange(piece(1, 2) bit:: piece(2, 2),0,3)

     rule start5 => env("a") ~> bitRange(piece(bitRange(piece(0, 0) bit:: 1, 0, 0), 1), 0, 0)

     rule start6 => env("a") ~> bitRange(piece(bitRange((piece(0,0) bit::
            piece(1,2)) bit:: piece(2,4), 5, 7), 3) bit::
            piece(bitRange((piece(0,0) bit:: piece(1,2))
            bit:: piece(2,4), 0, 4), 3),9,9)

     rule start7 => env("a") ~> dataList(ListItem(bitRange(piece(0,0),0,7))
            ListItem(piece(1,1)))

     rule start8 => env("a") ~> dataList(ListItem(piece(bitRange((piece(0,0) bit:: piece(1,2))
            bit:: piece(2,4), 5, 7), 3))
            ListItem(piece(bitRange((piece(0,0)
            bit:: piece(1,2)) bit:: piece(2,4), 0, 4), 3)))

     rule start9 => env("a") ~> (piece(piece(1,1) bit::
            piece(1,1),2) bit:: piece(1, 1)) bit::
            (piece(1, 1) bit:: piece(piece(1,1)
            bit:: piece(1,1), 2))

     rule start10 => env("a") ~> dataList(ListItem(piece(piece(1,1)
            bit:: piece(1,1),2)) ListItem(piece(1, 1))
            ListItem(piece(1, 1) bit::
            piece(piece(1,1) bit:: piece(1,1), 2)))

     rule start11 => env("a") ~> dataList(ListItem(piece(piece(1,1)
            bit:: piece(1,1),2)) ListItem(piece(bitRange((piece(0,0)
            bit:: piece(1,2)) bit:: piece(2,4), 5, 7), 3)
            bit:: piece(bitRange((piece(0,0) bit:: piece(1,2))
            bit:: piece(2,4), 0, 4), 3)) ListItem(piece(1, 1)
            bit:: piece(piece(1,1) bit:: piece(1,1), 2)))

endmodule
