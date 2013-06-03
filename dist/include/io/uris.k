require "builtins/builtins.k"

module URIS 
  imports BUILTIN-HOOKS
  imports #K-PARSER-INTERFACE
  imports #K-PRINTER-INTERFACE
 
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
 
  syntax K ::= "#fPutByte" "(" Int "," Int ")"      [function, klabel(#fPutByte)]
             | "#flush" "(" Int ")"                 [function, klabel(#flush)]
             | "#fReadByte" "(" Int ")"             [function, klabel(#fReadByte)]
             | "#fReadBytes" "(" Int "," Int ")"    [function, klabel(#fReadBytes)]
             | "#fPutBytes" "(" Int "," String ")" [function, klabel(#fPutBytes)]
 
  syntax KList ::= "#stat" "(" String ")" [function]
                 | "#lstat" "(" String ")" [function]
                 | "#opendir" "(" String ")" [function]

  syntax K ::= "#parse" "(" String "," String ")" [function, klabel(#parse)]
  rule #open(S:String) => String2Int((#tcpRequest("open\001" +String S +String "\001"))::K) [function, anywhere]

  rule #close(N:Int) 
      => String2DotK((#tcpRequest("close\001" +String Int2String(N) +String "\001"))::K) [function, anywhere]

  syntax K ::= "String2DotK" "(" TCPAnswer ")"  [function, klabel(String2DotK)]
  rule String2DotK(S:String) => #ioError(#retrieveTCPError(S)) when #isTCPError(S) [function, anywhere]
  rule String2DotK(S:String) => .K when notBool(#isTCPError(S)) [function, anywhere]
  rule String2DotK(E:TCPError) => E 


  rule String2Bool("0") => false [anywhere]
  rule String2Bool("false") => false [anywhere]
  rule String2Bool("1") => true [anywhere]
  rule String2Bool("true") => true [anywhere]

  rule #flush(N:Int) => String2DotK((#tcpRequest("flush\001" +String Int2String(N) +String "\001"))::K) [function, anywhere]

  rule #tell(N:Int) => String2DotK((#tcpRequest("position\001" +String Int2String(N) +String "\001"))::K) [function, anywhere]

  rule #tell(N:Int) => String2Int((#tcpRequest("tell\001" +String Int2String(N) +String "\001"))::K) [function, anywhere]

  rule #seek(N:Int,P:Int) 
      => String2DotK((#tcpRequest("seek\001" +String Int2String(N) +String "\001"
                              +String Int2String(P) +String "\001"))::K) [function, anywhere]

  rule #reopen(N:Int,S:String) 
      => String2DotK((#tcpRequest("reopen\001" +String Int2String(N) +String "\001"
                              +String S +String "\001"))::K) [function, anywhere]

  syntax Int ::= "#stdin"   [function] 
                | "#stdout" [function]
                | "#stderr" [function] 
  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

  syntax K ::= "#readByte" "(" ")" 
             | "#peekByte" "(" ")"
             | "#putByte" "(" Int ")"
             | "#eof" "(" ")"
  rule #readByte() => #fReadByte(#stdin) [function, anywhere]

  rule #fReadByte(N:Int) 
      => #string2Int(#tcpRequest("readbyte\001" +String Int2String(N) +String "\001")) [function, anywhere]

  rule #fReadBytes(N:Int, NumBytes:Int)
      => #tcpRequest("readbytes\001" +String Int2String(N) +String "\001" +String Int2String(NumBytes) +String "\001") [function, anywhere]

  syntax K ::= "#string2Int" "(" K ")"   [function, klabel(#string2Int)]

  rule #string2Int(S:String) => String2Int(S) when lengthString(S) >=Int 0 [function, anywhere]
  rule #string2Int(#EOF) => #EOF [function, anywhere]

  rule #putByte(B:Int) => #fPutByte(#stdout,B) [function, anywhere]

  rule #fPutByte(N:Int,B:Int)
    => String2DotK((#tcpRequest("writebyte\001" +String Int2String(N) +String "\001"
                              +String Int2String(B) +String "\001"))::K) [function, anywhere]

  rule #fPutBytes(N:Int,S:String)
    => String2DotK((#tcpRequest("writebytes\001" +String Int2String(N) +String "\001"
                              +String S +String "\001"))::K) [function, anywhere]

  rule #peekByte() => #fPeekByte(#stdin) [function, anywhere]
  rule #fPeekByte(N:Int)
    => String2Int((#tcpRequest("peek\001" +String Int2String(N) +String "\001"))::K) [function, anywhere]

  rule #eof() => #fEof(#stdin) [function, anywhere]
  rule #fEof(N:Int)
    => String2Bool((#tcpRequest("eof\001" +String Int2String(N) +String "\001"))::K) [function, anywhere]

  rule #stat(S:String)
    => #statTypes(#string2klist((#tcpRequest("stat\001" +String S +String "\001true\001"))::K))

  rule #lstat(S:String)
    => #statTypes(#string2klist((#tcpRequest("stat\001" +String S +String "\001false\001"))::K))

  rule #opendir(S:String) => #string2klist((#tcpRequest("opendir\001" +String S +String "\001"))::K)

  syntax KList ::= #string2klist(String) [function]
  rule #string2klist(S:String) => substrString(S, 0, findString(S, "\001", 0)) ,, #string2klist(substrString(S, findString(S, "\001", 0) +Int 1, lengthString(S))) when findString(S, "\001", 0) =/=Int -1
  rule #string2klist(S:String) => S when findString(S, "\001", 0) ==Int -1
  rule #string2klist(K) => K when isString(K) =/=K true

  syntax KList ::= #statTypes(KList) [function]
  rule #statTypes(S1:String,,S2:String,,S3:String,,S4:String,,S5:String,,S6:String,,S7:String,,S8:String,,S9:String,,S10:String,,S11:String,,S12:String) => String2Int(S1),,String2Int(S2),,String2Int(S3),,String2Bool(S4),,String2Bool(S5),,String2Bool(S6),,String2Int(S7),,String2Int(S8),,String2Int(S9),,String2Int(S10),,String2Int(S11),,String2Int(S12)
  rule #statTypes(K:K) => K

  syntax K ::= "#readChar" "(" ")"   [function, klabel(#readChar)]
  //declare  #readChar() : -> K 
  rule #readChar() => #fReadChar(#stdin) [function, anywhere]

  syntax K ::= "#fReadChar" "(" Int ")"   [function, klabel(#fReadChar)]
  rule #fReadChar(N:Int) => #charString(#fReadByte(N)) [function, anywhere]

  syntax K ::= "#charString" "(" K ")"   [function, klabel(#charString)]
  rule #charString(N:Int) => charString(N) [function, anywhere]
  rule #charString(#EOF) => #EOF [function, anywhere]

  syntax K ::= "#printChar" "(" K ")"   [function, klabel(#printChar)]
  rule #printChar(C:K) => #fPrintChar(#stdout,C)
        when isChar(C) [anywhere]

  syntax K ::= "#fPrintChar" "(" Int "," K ")"   [function, klabel(#fPrintChar)]
  rule #fPrintChar(N:Int,C:String) => #fPutByte(N,asciiString(C)) 
        when isChar(C) [anywhere]

  rule #buffer(.K => Int2String(I)) (ListItem(I:Int) => .List)
  rule #buffer(.K => Float2String(F)) (ListItem(F:Float) => .List)
  rule #buffer(.K => S) (ListItem(S:String) => .List)

  rule #buffer(Buffer:String => Buffer +String Int2String(I)) (ListItem(I:Int) => .List)
  rule #buffer(Buffer:String => Buffer +String Float2String(F)) (ListItem(F:Float) => .List)
  rule #buffer(Buffer:String => Buffer +String S) (ListItem(S:String) => .List)

  // Send first char from the buffer to the server
  rule #ostream(N:Int) (.List =>  ListItem(#fPutBytes(N,S))
       #removeCharsUponAck(lengthString(S))) #buffer(S:String)
    when S =/=String ""
  // Flush when the buffer becomes empty
  rule #ostream(N:Int) (.List => ListItem(#flush(N))) #buffer("" => .K)

  rule #ostream(_:Int) (ListItem(.K) => .List) 
  // consume a char from the buffer only on succesfull communication 
  rule #ostream(_:Int) (#removeCharsUponAck(I:Int) => .List) #buffer(S:String => substrString(S,I, lengthString(S)))
 
  syntax List ::= "#removeCharsUponAck" "(" Int ")"
  
  syntax List ::= "#parseInput" "(" String "," K ")"   [cons(List1ParseSyn)]

/*
  // base values for each type
  syntax K ::= `#defaultValue ( String ) 
  rule #defaultValue("Int") = 0
  rule #defaultValue("String") = "" 
  rule #defaultValue("Float") = 0.0
*/
  
  // Parsing a character
  rule (#parseInput("#Char",_) => .List) ListItem(C:String)
         when isChar(C)

  // Skipping initial whitespace if reading more than a character
  rule #parseInput(S:String,.K) (ListItem(C) => .List) 
        when S =/=String "#Char" andBool #isWhiteSpace(C) andBool isString(C)


  // Read a token
  rule #parseInput(S:String,.K => "") ListItem(C)
        when S =/=String "#Char" andBool notBool(#isWhiteSpace(C)) andBool isString(C)
        
  rule #parseInput(_:String, S:String => S:String +String C) (ListItem(C) => .List) 
    when notBool(#isWhiteSpace(C)) andBool isString(C)

  // Upon encountering again whitespace, convert token
  rule #parseInput(SType:String,S:String) ListItem(C) => #convertToken(SType, S)
    when #isWhiteSpace(C) andBool isString(C)

  rule (#parseInput(SType:String,S:String) => #convertToken(SType, S)) ListItem(#EOF)
  
  syntax List ::= "#convertToken" "(" String "," String ")"
  rule #convertToken(Type:String,S:String) => ListItem(#parseToken(Type, S))

  
 /*   C++ -like parsing for ints. 
  rule #parse("Int",I:Int => 10 *Int I +Int String2Int(C)) ListItem(C:String)
    when #isDigit(C:String)
  */

  syntax List ::= "#buffer" "(" K ")"           [cons(List1IOBufferSyn)]

  // Initial input string is assumed wrapped in an #buffer wrapper an one character is retreved from it at a time
  rule #parseInput(_:String,_) (.List => ListItem(substrString(S:String,0,1))) 
       #buffer(S:String => substrString(S,1,lengthString(S)))
    when S =/=String ""
    
  rule #buffer("" => .K) #istream(_:Int)

  // I fthe buffer becomes empty, read from the input stream
  rule #parseInput(_:String,_) (.List => ListItem(#fReadChar(N:Int))) #buffer(.K) #istream(N)

  syntax List ::= "#istream" "(" Int ")"        [cons(List1InputStreamSyn)]
                | "#ostream" "(" Int ")"        [cons(List1OutputStreamSyn)]
  syntax List ::= "#noIO"
  rule #noIO #istream(_:Int) => .List
  rule #ostream(_:Int) #noIO => .List

// ------------------------------
// Dynamic parsing

  rule #parse(StringToParse, Sort) => String2K((#tcpRequest("parse\001" +String Sort +String "\001" +String StringToParse +String "\001"))::K)

  syntax K ::= String2K(String) [function, hook(#K-PARSER:string2k)]
  syntax Bag ::= String2Bag(String) [function, hook(#K-PARSER:string2bag)]
  syntax String ::= K2String(K) [function, hook(#K-PRINTER:k2string)]
                  | Bag2String(Bag) [function, hook(#K-PRINTER:bag2string)]

  rule String2K((#noparse)::K) => #noparse

endmodule
