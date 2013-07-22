require "builtins/builtins.k"

module URIS 
  imports BUILTIN-HOOKS
  imports #K-PARSER-INTERFACE
  imports #K-PRINTER-INTERFACE
 
// B, N, and P are really supposed to be Nat
  syntax K ::= "#open" "(" String ")" [function]
             | "#open" "(" String "," String ")" [function, hook(#IO:#open)]
             | "#reopen" "(" Int "," String ")" [function, hook(#IO:#reopen)]
             | "#close" "(" Int ")" [function, hook(#IO:#close)]
             | "#eof" "(" Int ")"  [function, hook(#IO:#eof)]
             | "#tell" "(" Int ")" [function, hook(#IO:#tell)] 
             | "#seek" "(" Int "," Int ")" [function, hook(#IO:#seek)]
             | "#peek" "(" Int ")" [function, hook(#IO:#peek)]
             | "#putc" "(" Int "," Int ")"      [function, hook(#IO:#putc)]
             | "#flush" "(" Int ")"                 [function, hook(#IO:#flush)]
             | "#getc" "(" Int ")"             [function, hook(#IO:getc)]
             | "#read" "(" Int "," Int ")"    [function, hook(#IO:#read)]
             | "#write" "(" Int "," String ")" [function, hook(#IO:#write)]
             
  syntax K ::= "#ioError" "(" String ")"
 
  syntax KList ::= "#stat" "(" String ")" [function, hook(#IO:#stat)]
                 | "#lstat" "(" String ")" [function, hook(#IO:#lstat)]
                 | "#opendir" "(" String ")" [function, hook(#IO:#opendir)]

  syntax K ::= "#parse" "(" String "," String ")" [function, klabel(#parse), hook(#K-PARSER:#parse)]
  rule #open(S:String) => #open(S:String, "w")
  rule #open(S:String, Mode:String) => String2Int((#tcpRequest("open\x01file:" +String S +String "\x01" +String Mode +String "\x01"))::K)

  rule #close(N:Int) 
      => String2DotK((#tcpRequest("close\x01" +String Int2String(N) +String "\x01"))::K)

  syntax K ::= String2DotK(TCPAnswer)  [function]
  rule String2DotK(S:String) => #ioError(#retrieveTCPError(S)) when #isTCPError(S)
  rule String2DotK(S:String) => .K when notBool(#isTCPError(S))
  rule String2DotK(E:TCPError) => E 

  syntax Bool ::= String2Bool(TCPAnswer) [function]
  rule String2Bool("0") => false
  rule String2Bool("false") => false
  rule String2Bool("1") => true
  rule String2Bool("true") => true

  rule #flush(N:Int) => String2DotK((#tcpRequest("flush\x01" +String Int2String(N) +String "\x01"))::K)

  rule #tell(N:Int) => String2DotK((#tcpRequest("position\x01" +String Int2String(N) +String "\x01"))::K)

  rule #seek(N:Int,P:Int) 
      => String2DotK((#tcpRequest("seek\x01" +String Int2String(N) +String "\x01"
                              +String Int2String(P) +String "\x01"))::K)

  rule #reopen(N:Int,S:String) 
      => String2DotK((#tcpRequest("reopen\x01" +String Int2String(N) +String "\x01"
                              +String S +String "\x01"))::K)

  syntax Int ::= "#stdin"   [function] 
                | "#stdout" [function]
                | "#stderr" [function] 
  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

  rule #getc(N:Int) 
      => #string2Int(#tcpRequest("readbyte\x01" +String Int2String(N) +String "\x01"))

  rule #read(N:Int, NumBytes:Int)
      => #tcpRequest("readbytes\x01" +String Int2String(N) +String "\x01" +String Int2String(NumBytes) +String "\x01")

  syntax K ::= "#string2Int" "(" K ")"   [function, klabel(#string2Int)]

  rule #string2Int(S:String) => String2Int(S) when lengthString(S) >=Int 0
  rule #string2Int(#EOF) => #EOF

  rule #putc(N:Int,B:Int)
    => String2DotK((#tcpRequest("writebyte\x01" +String Int2String(N) +String "\x01"
                              +String Int2String(B) +String "\x01"))::K)

  rule #write(N:Int,S:String)
    => String2DotK((#tcpRequest("writebytes\x01" +String Int2String(N) +String "\x01"
                              +String S +String "\x01"))::K)

  rule #peek(N:Int)
    => String2Int((#tcpRequest("peek\x01" +String Int2String(N) +String "\x01"))::K)

  rule #eof(N:Int)
    => String2Bool((#tcpRequest("eof\x01" +String Int2String(N) +String "\x01"))::K)

  rule #stat(S:String)
    => #statTypes(#string2klist((#tcpRequest("stat\x01" +String S +String "\x01true\x01"))::K))

  rule #lstat(S:String)
    => #statTypes(#string2klist((#tcpRequest("stat\x01" +String S +String "\x01false\x01"))::K))

  rule #opendir(S:String) => #string2klist((#tcpRequest("opendir\x01" +String S +String "\x01"))::K)

  syntax KList ::= #string2klist(String) [function]
  rule #string2klist(S:String) => substrString(S, 0, findString(S, "\x01", 0)) ,, #string2klist(substrString(S, findString(S, "\x01", 0) +Int 1, lengthString(S))) when findString(S, "\x01", 0) =/=Int -1
  rule #string2klist(S:String) => S when findString(S, "\x01", 0) ==Int -1
  rule #string2klist(K:K) => K when isString(K) =/=K true

  syntax KList ::= #statTypes(KList) [function]
  rule #statTypes(S1:String,,S2:String,,S3:String,,S4:String,,S5:String,,S6:String,,S7:String,,S8:String,,S9:String,,S10:String,,S11:String,,S12:String) => String2Int(S1),,String2Int(S2),,String2Int(S3),,String2Bool(S4),,String2Bool(S5),,String2Bool(S6),,String2Int(S7),,String2Int(S8),,String2Int(S9),,String2Int(S10),,String2Int(S11),,String2Int(S12)
  rule #statTypes(K:K) => K

  rule #buffer(Buffer => Buffer +String Float2String(F)) (ListItem(F:Float) => .List)
  rule #buffer(Buffer => Buffer +String Int2String(I)) (ListItem(I:Int) => .List)
  rule #buffer(Buffer => Buffer +String S) (ListItem(S:String) => .List)

  // Send first char from the buffer to the server
  rule #ostream((. => #write(N, S) ~> #flush(N)) ~> N:Int) #buffer(S:String => "")
    when S =/=String ""

  syntax ListItem ::= "#parseInput" "(" String "," String ")"   [cons(ListItem1ParseSyn)]

 /*   C++ -like parsing for ints. 
  rule #parse("Int",I:Int => 10 *Int I +Int String2Int(C)) ListItem(C:String)
    when #isDigit(C:String)
  */

  syntax ListItem ::= "#buffer" "(" K ")"           [cons(ListItem1IOBufferSyn)]

  // read one character at a time until we read whitespace
  rule #parseInput(Sort:String, Delimiters:String) #buffer(S => S +String chrChar(#getc(N))) #istream(N) when findChar(S, Delimiters, 0) ==Int -1

  // when we reach whitespace, if it parses create a ListItem
  rule (#parseInput("String", Delimiters:String) => ListItem(S)) #buffer(S:String => "") when findChar(S, Delimiters, 0) =/=Int -1
  rule (#parseInput(Sort:String, Delimiters:String) => ListItem(#parse(S, Sort))) #buffer(S:String => "") when findChar(S, Delimiters, 0) =/=Int -1 andBool Sort =/=String "String"
  
  syntax ListItem ::= "#istream" "(" Int ")"        [cons(ListItem1InputStreamSyn)]
                    | "#ostream" "(" Int ")"        [cons(ListItem1OutputStreamSyn)]
  syntax ListItem ::= "#noIO"
  rule #noIO #istream(_:Int) => .List
  rule #ostream(_:Int) #noIO => .List

// ------------------------------
// Dynamic parsing

  rule #parse(StringToParse:String, Sort:String) => String2K((#tcpRequest("parse\x01" +String Sort +String "\x01" +String StringToParse +String "\x01"))::K)

  syntax K ::= String2K(String) [function, hook(#K-PARSER:string2k)]
  syntax Bag ::= String2Bag(String) [function, hook(#K-PARSER:string2bag)]
  syntax String ::= K2String(K) [function, hook(#K-PRINTER:k2string)]
                  | Bag2String(Bag) [function, hook(#K-PRINTER:bag2string)]

  rule String2K((#noparse)::K) => #noparse [simplification]

endmodule
