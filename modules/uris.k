module URIS 
  imports #TCP-INTERFACE 
  syntax K ::= #String | #Int | #Float
             | `#open ( #String ) 
             | `#reopen ( #Nat , #String ) 
             | `#close ( #Nat ) 
             | `#fEof ( #Nat )
             | `#tell ( #Nat ) 
             | `#seek ( #Nat , #Nat )
             | `#fPeekByte ( #Nat )
             | `String2Bool ( #String )
             | `#ioError ( #String )

  declare #fPutByte : #Nat  #Nat -> K
  declare #flush : #Nat -> K
  declare #fReadByte : #Nat -> K
            
  syntax KResult ::= `#EOF 
  rule #errorTCPSyntax("EOF") => #EOF [anywhere]

  define #open(S:#String) => String2Int(#tcpRequest("open#" +String S +String "#")) 

  define #close(N:#Nat) => String2DotK(#tcpRequest("close#" +String Int2String(N) +String "#"))

  declare String2DotK : #String -> K
  define String2DotK(#errorTCPSyntax(S)) => #ioError(S)
  define String2DotK(S) => .K when notBool(#isTCPError(S))
  
  rule String2Bool("0") => false [anywhere]
  rule String2Bool("1") => true [anywhere]

  define #flush(N) => String2DotK(#tcpRequest("flush#" +String Int2String(N) +String "#"))

  define #tell(N) => String2DotK(#tcpRequest("position#" +String Int2String(N) +String "#"))

  define #tell(N) => String2Int(#tcpRequest("tell#" +String Int2String(N) +String "#"))

  define #seek(N,P:#Nat) => String2DotK(#tcpRequest("seek#" +String Int2String(N) +String "#"
                              +String Int2String(P) +String "#"))

  define #reopen(N,S) => String2DotK(#tcpRequest("reopen#" +String Int2String(N) +String "#"
                              +String S +String "#"))

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
  define #readByte() => #fReadByte(#stdin)

  define #fReadByte(N) => #string2Int(#tcpRequest("readbyte#" +String Int2String(N) +String "#"))

  declare #string2Int : K -> K
  define #string2Int(S) => String2Int(S) when lengthString(S) >=Int 0

  define #putByte(B) => #fPutByte(#stdout,B)

  define #fPutByte(N,B:#Nat)
    => String2DotK(#tcpRequest("writebyte#" +String Int2String(N) +String "#"
                              +String Int2String(B) +String "#"))

  define #peekByte() => #fPeekByte(#stdin)
  define #fPeekByte(N)
    => String2Int(#tcpRequest("peek#" +String Int2String(N) +String "#"))

  define #eof() => #fEof(#stdin)
  define #fEof(N)
    => String2Bool(#tcpRequest("eof#" +String Int2String(N) +String "#"))

  declare  #readChar() : -> K 
  define #readChar() => #fReadChar(#stdin)

  declare #fReadChar : #Nat -> K
  define #fReadChar(N) => #charString(#fReadByte(N))

  declare #charString : K -> K 
  rule #charString(N:#Nat) => charString(N) [anywhere]

  declare #printChar : K -> K 
  rule #printChar(C) => #fPrintChar(#stdout,C) [anywhere]

  declare #fPrintChar : #Nat K -> K 
  rule #fPrintChar(N,C:#Char) => #fPutByte(N,asciiString(C)) [anywhere]

  rule #buffer(.K => Int2String(I)) (ListItem(I:#Int) => .List)
  rule #buffer(.K => Float2String(F)) (ListItem(F:#Float) => .List)
  rule #buffer(.K => S) (ListItem(S:#String) => .List)

  rule #buffer(Buffer:#String => Buffer +String Int2String(I)) (ListItem(I:#Int) => .List)
  rule #buffer(Buffer:#String => Buffer +String Float2String(F)) (ListItem(F:#Float) => .List)
  rule #buffer(Buffer:#String => Buffer +String S) (ListItem(S:#String) => .List)

  // Send first char from the buffer to the server
  rule #ostream(N:#Nat) (.List =>  ListItem(#fPrintChar(N,substrString(S,0,1)))
       #removeCharUponAck) #buffer(S:#String)
    when S =/=Bool ""
  // Flush when the buffer becomes empty
  rule #ostream(N:#Nat) (.List => ListItem(#flush(N))) #buffer("" => .K)

  rule #ostream(_:#Nat) (ListItem(.K) => .List) 
  //consume a char from the buffer only on succesfull communication 
  rule #ostream(_:#Nat) (#removeCharUponAck => .List) #buffer(S:#String => substrString(S,1, lengthString(S)))
 
  syntax List ::= `#removeCharUponAck
  
  syntax List ::= `#parse ( #String , K )

/*
  // base values for each type
  syntax K ::= `#defaultValue ( #String ) 
  rule #defaultValue("#Int") = 0
  rule #defaultValue("#String") = "" 
  rule #defaultValue("#Float") = 0.0
*/
  
  // Parsing a character
  rule (#parse("#Char",_) => .List) ListItem(C:#Char)

  // Skipping initial whitespace if reading more than a character
  rule #parse(S:#String,.K) (ListItem(C:#Char) => .List) 
    when S =/=Bool "#Char" andBool #isWhiteSpace(C)


  // Read a token
  rule #parse(S:#String,.K => "") ListItem(C:#Char) 
    when S =/=Bool "#Char" andBool notBool(#isWhiteSpace(C))
  rule #parse(_:#String, S:#String => S:#String +String C) (ListItem(C:#Char) => .List) 
    when notBool(#isWhiteSpace(C))

  // Upon encountering again whitespace, convert token
  rule #parse(SType:#String,S:#String) ListItem(C:#Char) => #convertToken(SType, S)
    when #isWhiteSpace(C)
  
  syntax List ::= `#convertToken ( #String , #String )
  rule #convertToken("#Int",S:#String) => ListItem(String2Int(S +String "0") /Int 10)
  rule #convertToken("#Float",S:#String) => ListItem(String2Float(S))
  rule #convertToken("#String",S:#String) => ListItem(S)

  rule String2Int("00") => 0  [anywhere]

  
 /*   C++ -like parsing for ints.
  rule parse("#Int",I:#Int => 10 *Int I +Int String2Int(C)) ListItem(C:#Char)
    when #isDigit(C:#Char)
  */

  syntax List ::= `#buffer ( K )

  // Initial input string is assumed wrapped in an #buffer wrapper an one character is retreved from it at a time
  rule #parse(_:#String,_) (.List => ListItem(substrString(S,0,1))) 
       #buffer(S:#String => substrString(S,1,lengthString(S)))
    when S =/=Bool ""
  rule #buffer("" => .K) #istream(_:#Nat)

  // I fthe buffer becomes empty, read from the input stream
  rule #parse(_:#String,_) (.List => ListItem(#fReadChar(N))) #buffer(.K) #istream(N)

  syntax List ::= `#istream ( #Nat ) | `#ostream ( #Nat ) 
  syntax List ::= `#noIO
  rule #noIO #istream(_:#Nat) => .List
  rule #ostream(_:#Nat) #noIO => .List
end module
