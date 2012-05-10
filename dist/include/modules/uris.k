require "builtins/builtins.k"

module URIS 
  imports BUILTIN-HOOKS
// B, N, and P are really supposed to be Nat
  syntax K ::= String | Int | Float
             | "#open" "(" String ")"
             | "#reopen" "(" Int "," String ")"
             | "#close" "(" Int ")"
             | "#fEof" "(" Int ")"
             | "#tell" "(" Int ")"
             | "#seek" "(" Int "," Int ")"
             | "#fPeekByte" "(" Int ")"
             | "String2Bool" "(" String ")"
             | "#ioError" "(" String ")"

  syntax K ::= "#fPutByte" "(" Int "," Int ")"   [function, klabel(#fPutByte)]
             | "#flush" "(" Int ")"              [function, klabel(#flush)]
             | "#fReadByte" "(" Int ")"          [function, klabel(#fReadByte)]

            
  rule #open(S:String) => String2Int(#tcpRequest("open#" +String S +String "#")) [function, anywhere]

  rule #close(N:Int) 
      => String2DotK(#tcpRequest("close#" +String Int2String(N) +String "#")) [function, anywhere]

  syntax K ::= "String2DotK" "(" String ")"  [function, klabel(String2DotK)]
  rule String2DotK(S) => #ioError(#retrieveTCPError(S)) when #isTCPError(S) [function, anywhere]
  rule String2DotK(S) => .K when notBool(#isTCPError(S)) [function, anywhere]
  

  rule String2Bool("0") => false [anywhere]
  rule String2Bool("1") => true [anywhere]

  rule #flush(N) => String2DotK(#tcpRequest("flush#" +String Int2String(N) +String "#")) [function, anywhere]

  rule #tell(N) => String2DotK(#tcpRequest("position#" +String Int2String(N) +String "#")) [function, anywhere]

  rule #tell(N) => String2Int(#tcpRequest("tell#" +String Int2String(N) +String "#")) [function, anywhere]

  rule #seek(N,P:Int) 
      => String2DotK(#tcpRequest("seek#" +String Int2String(N) +String "#"
                              +String Int2String(P) +String "#")) [function, anywhere]

  rule #reopen(N,S) 
      => String2DotK(#tcpRequest("reopen#" +String Int2String(N) +String "#"
                              +String S +String "#")) [function, anywhere]

  syntax Int ::= "#stdin" 
                | "#stdout" 
                | "#stderr"
  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

  syntax K ::= "#readByte" "(" ")" 
             | "#peekByte" "(" ")"
             | "#putByte" "(" Int ")"
             | "#eof" "(" ")"
  rule #readByte() => #fReadByte(#stdin) [function, anywhere]

  rule #fReadByte(N) 
      => #string2Int(#tcpRequest("readbyte#" +String Int2String(N) +String "#")) [function, anywhere]

  syntax K ::= "#string2Int" "(" K ")"   [function, klabel(#string2Int)]

  rule #string2Int(S) => String2Int(S) when lengthString(S) >=Int 0 [function, anywhere]
  rule #string2Int(#EOF) => #EOF [function, anywhere]

  rule #putByte(B) => #fPutByte(#stdout,B) [function, anywhere]

  rule #fPutByte(N,B:Int)
    => String2DotK(#tcpRequest("writebyte#" +String Int2String(N) +String "#"
                              +String Int2String(B) +String "#")) [function, anywhere]

  rule #peekByte() => #fPeekByte(#stdin) [function, anywhere]
  rule #fPeekByte(N)
    => String2Int(#tcpRequest("peek#" +String Int2String(N) +String "#")) [function, anywhere]

  rule #eof() => #fEof(#stdin) [function, anywhere]
  rule #fEof(N)
    => String2Bool(#tcpRequest("eof#" +String Int2String(N) +String "#")) [function, anywhere]

  syntax K ::= "#readChar" "(" ")"   [function, klabel(#readChar)]
  //declare  #readChar() : -> K 
  rule #readChar() => #fReadChar(#stdin) [function, anywhere]

  syntax K ::= "#fReadChar" "(" Int ")"   [function, klabel(#fReadChar)]
  rule #fReadChar(N) => #charString(#fReadByte(N)) [function, anywhere]

  syntax K ::= "#charString" "(" K ")"   [function, klabel(#charString)]
  rule #charString(N:Int) => charString(N) [function, anywhere]
  rule #charString(#EOF) => #EOF [function, anywhere]

  syntax K ::= "#printChar" "(" K ")"   [function, klabel(#printChar)]
  rule #printChar(C) => #fPrintChar(#stdout,C)
        when isChar(C) [anywhere]

  syntax K ::= "#fPrintChar" "(" Int "," K ")"   [function, klabel(#fPrintChar)]
  rule #fPrintChar(N,C:String) => #fPutByte(N,asciiString(C)) 
        when isChar(C) [anywhere]

  rule #buffer(.K => Int2String(I)) (ListItem(I:Int) => .List)
  rule #buffer(.K => Float2String(F)) (ListItem(F:Float) => .List)
  rule #buffer(.K => S) (ListItem(S:String) => .List)

  rule #buffer(Buffer:String => Buffer +String Int2String(I)) (ListItem(I:Int) => .List)
  rule #buffer(Buffer:String => Buffer +String Float2String(F)) (ListItem(F:Float) => .List)
  rule #buffer(Buffer:String => Buffer +String S) (ListItem(S:String) => .List)

  // Send first char from the buffer to the server
  rule #ostream(N:Int) (.List =>  ListItem(#fPrintChar(N,substrString(S,0,1)))
       #removeCharUponAck) #buffer(S:String)
    when S =/=String ""
  // Flush when the buffer becomes empty
  rule #ostream(N:Int) (.List => ListItem(#flush(N))) #buffer("" => .K)

  rule #ostream(_:Int) (ListItem(.K) => .List) 
  // consume a char from the buffer only on succesfull communication 
  rule #ostream(_:Int) (#removeCharUponAck => .List) #buffer(S:String => substrString(S,1, lengthString(S)))
 
  syntax List ::= "#removeCharUponAck"
  
  syntax List ::= "#parse" "(" String "," K ")"

/*
  // base values for each type
  syntax K ::= `#defaultValue ( String ) 
  rule #defaultValue("Int") = 0
  rule #defaultValue("String") = "" 
  rule #defaultValue("Float") = 0.0
*/
  
  // Parsing a character
  rule (#parse("#Char",_) => .List) ListItem(C:String)
         when isChar(C)

  // Skipping initial whitespace if reading more than a character
  rule #parse(S:String,.K) (ListItem(C:String) => .List) 
        when S =/=String "#Char" andBool #isWhiteSpace(C)


  // Read a token
  rule #parse(S:String,.K => "") ListItem(C:String) 
        when S =/=String "#Char" andBool notBool(#isWhiteSpace(C))
  rule #parse(_:String, S:String => S:String +String C) (ListItem(C:String) => .List) 
    when notBool(#isWhiteSpace(C))

  // Upon encountering again whitespace, convert token
  rule #parse(SType:String,S:String) ListItem(C:String) => #convertToken(SType, S)
    when #isWhiteSpace(C)

  rule (#parse(SType:String,S:String) => #convertToken(SType, S)) ListItem(#EOF)
  
  syntax List ::= "#convertToken" "(" String "," String ")"
  rule #convertToken("Int",S:String) => ListItem(String2Int(S +String "0") /Int 10)
  rule #convertToken("Float",S:String) => ListItem(String2Float(S))
  rule #convertToken("String",S:String) => ListItem(S)

  rule String2Int("00") => 0  [anywhere]

  
 /*   C++ -like parsing for ints.
  rule parse("Int",I:Int => 10 *Int I +Int String2Int(C)) ListItem(C:String)
    when #isDigit(C:String)
  */

  syntax List ::= "#buffer" "(" K ")"

  // Initial input string is assumed wrapped in an #buffer wrapper an one character is retreved from it at a time
  rule #parse(_:String,_) (.List => ListItem(substrString(S,0,1))) 
       #buffer(S:String => substrString(S,1,lengthString(S)))
    when S =/=String ""
  rule #buffer("" => .K) #istream(_:Int)

  // I fthe buffer becomes empty, read from the input stream
  rule #parse(_:String,_) (.List => ListItem(#fReadChar(N))) #buffer(.K) #istream(N)

  syntax List ::= "#istream" "(" Int ")" | "#ostream" "(" Int ")" 
  syntax List ::= "#noIO"
  rule #noIO #istream(_:Int) => .List
  rule #ostream(_:Int) #noIO => .List
endmodule
