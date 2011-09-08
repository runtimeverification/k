module URIS 
  imports #TCP-INTERFACE 
  syntax K ::= #String | #Int | #Float
             | `#open ( #String ) 
             | `#reopen ( #Nat , #String ) 
             | `#close ( #Nat ) 
             | `#fEof ( #Nat )
             | `#flush ( #Nat )
             | `#tell ( #Nat ) 
             | `#seek ( #Nat , #Nat )
             | `#fPeekByte ( #Nat )
             | `#fReadByte ( #Nat ) 
             | `#fPutByte ( #Nat , #Nat )
             | `String2DotK ( #String ) 
             | `String2Bool ( #String )
             | `#ioError ( #String )
            
  syntax KResult ::= `#EOF | #String
  rule errorTCPSyntax("EOF") => #EOF

  rule <k> #open(S:#String) 
    => String2Int(tcpRequest("open#" +String S +String "#")) ...</k>

  rule <k> #close(N:#Nat)
    => String2DotK(tcpRequest("close#" +String Int2String(N) +String "#"))
       ...</k>

  rule String2DotK(errorTCPSyntax(S)) => #ioError(S)
  rule String2DotK(S) => .K if notBool(#isTCPError(S))
  
  rule String2Bool("0") => false
  rule String2Bool("1") => true

  rule <k> #flush(N)
    => String2DotK(tcpRequest("flush#" +String Int2String(N) +String "#"))
    ...</k>

  rule <k> #tell(N)
    => String2DotK(tcpRequest("position#" +String Int2String(N) +String "#"))
    ...</k>

  rule <k> #tell(N)
    => String2Int(tcpRequest("tell#" +String Int2String(N) +String "#"))
    ...</k>

  rule <k> #seek(N,P:#Nat)
    => String2DotK(tcpRequest("seek#" +String Int2String(N) +String "#"
                              +String Int2String(P) +String "#"))
      ...</k>

  rule <k> #reopen(N,S)
    => String2DotK(tcpRequest("reopen#" +String Int2String(N) +String "#"
                              +String S +String "#"))
       ...</k>

  syntax #Nat ::= `#stdin 
                | `#stdout 
                | `#stderr
  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

  syntax K ::= `#readByte (  ) 
             | `#peekByte ( )
             | `#putByte ( #Nat )
             | `#eof ( )
  rule #readByte() => #fReadByte(#stdin)
  rule <k> #fReadByte(N)
    => String2Int(tcpRequest("readbyte#" +String Int2String(N) +String "#"))
        ...</k>

  rule #putByte(B) => #fPutByte(#stdout,B)
  rule <k> #fPutByte(N,B:#Nat)
    => String2DotK(tcpRequest("writebyte#" +String Int2String(N) +String "#"
                              +String Int2String(B) +String "#"))
       ...</k>

  rule #peekByte() => #fPeekByte(#stdin)
  rule <k> #fPeekByte(N)
    => String2Int(tcpRequest("peek#" +String Int2String(N) +String "#"))
       ...</k>

  rule #eof() => #fEof(#stdin)
  rule <k> #fEof(N)
    => String2Bool(tcpRequest("eof#" +String Int2String(N) +String "#"))
       ...</k>

  syntax K ::= `#readChar ( ) 
             | `#fReadChar ( #Nat )
  rule #readChar() => #fReadChar(#stdin)
  rule #fReadChar(N) => Ascii2Char(#fReadByte(N))

  syntax K ::= `Ascii2Char ( K ) [strict]
  rule Ascii2Char(N) => charString(N)

  syntax K ::= `#printChar ( K ) 
             | `#fPrintChar ( #Nat , K ) [strict(2)]
  rule #printChar(C) => #fPrintChar(#stdout,C)
  rule #fPrintChar(N,C:#Char) => #fPutByte(N,asciiString(C))

  syntax KLabel ::= `#printLn | `#print
                  | `#fPrintLn | `#fPrint
  rule #printLn(L:List{K}) => #fPrintLn(#stdout,,L) ~> #flush(#stdout)
  rule #fPrintLn(N,,L) => #fPrint(N,,L) ~> #fPrintChar(N,"\n")

  rule #print(L:List{K}) => #fPrint(#stdout,,L) ~> #flush(#stdout)
  rule #fPrint(N,,.List{K}) => .K

  rule #fPrint(N,,(I:#Int => Int2String(I)),,_)
  rule #fPrint(N,,(F:#Float => Float2String(F)),,_)

  rule #fPrint(N,,("" => .List{K}),,_)
  rule (. => #fPrintChar(N,substrString(S,0,1))) 
     ~> #fPrint(N,,(S => substrString(S,1,lengthString(S))),,_)
    if S =/=Bool ""

  syntax K ::= `#fReadToken ( #Nat ) 
             | `#readToken ( )
  rule #readToken() => #fReadToken(#stdin)
  rule #fReadToken(N) => #fNextToken(N, #fSkipWhiteSpace(N,#readChar()), "")

  syntax K ::= `#fSkipWhiteSpace ( #Nat , K ) [strict(2)]
  rule #fSkipWhiteSpace(_,#EOF) => #EOF
  rule #fSkipWhiteSpace(N,(C => #fReadChar(N))) if #isWhiteSpace(C)
  rule #fSkipWhiteSpace(_,C) => C if notBool(#isWhiteSpace(C))

  syntax K ::= `#fNextToken ( #Nat , K , #String ) [strict(2)]
  rule #fNextToken(N,(C => #fReadChar(N)), (S => S +String C)) 
    if notBool(#isWhiteSpace(C))
  rule #fNextToken(_,C,S) => S if #isWhiteSpace(C)
  rule #fNextToken(_,#EOF,S) => S

  syntax K ::= `#fReadInt ( #Nat ) 
             | `#readInt ( ) 
             | `#parseInt ( K ) [strict]
  rule #readInt() => #fReadInt(#stdin)
  rule #fReadInt(N) => #parseInt(#fReadToken(N))
  rule #parseInt(S) => String2Int(S)

  syntax K ::= `#fReadFloat ( #Nat ) 
             | `#readFloat ( ) 
             | `#parseFloat ( K ) [strict]
  rule #readFloat() => #fReadFloat(#stdin)
  rule #fReadFloat(N) => #parseFloat(#fReadToken(N))
  rule #parseFloat(S) => String2Float(S)

  syntax ListItem ::= `#istream ( #Nat , #String ) | `#ostream ( #Nat ) 
                    | `#fListRead | `#getResult ( Bag ) 
  syntax List ::= `#checkEmptyK ( Bag ) 
                | `#stream ( #String )


  rule #stream("stdin:/") => #istream(0,"#Int")
  rule #stream("stdout:/") => #ostream(1)

  rule < CL:CellLabel >
               (#fListRead => #getResult(<k> #fReadFloat(N) </k>)) 
               #istream(N:#Nat, "#Float") 
       </ CL >
  rule < CL:CellLabel >
                    (#fListRead => #getResult(<k> #fReadToken(N) </k>)) 
               #istream(N:#Nat, "#String") 
       </ CL >
  rule < CL:CellLabel >
                     (#fListRead => #getResult(<k> #fReadChar(N) </k>)) 
               #istream(N:#Nat, "#Char") 
       </ CL >
  rule < CL:CellLabel >
                     (.List => #getResult(<k> #fReadInt(N) </k>)) 
               #istream(N:#Nat, "#Int") 
       </ CL >

  rule < CL:CellLabel > #ostream(N:#Nat) 
                       (ListItem(K:K) => #checkEmptyK(<k> #fPrint(N,,K) ~> #flush(N) </k>)) 
                        RestL:List </ CL >

  rule #getResult(<k> S:#String </k>) => ListItem(S)
  rule #getResult(<k> C:#Char </k>) => ListItem(C)
  rule #getResult(<k> I:#Int </k>) => ListItem(I)
  rule #getResult(<k> F:#Float </k>) => ListItem(F)
  rule #checkEmptyK(<k> .K </k>) => .List

  syntax K ::= `#end | `#done
  rule <k> #end => String2DotK(tcpRequest("end#")) ~> #done </k>
  
end module
