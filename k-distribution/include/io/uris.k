// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "builtins/builtins.k"
require "io/io.k"
require "io/tcp.k"

module URIS
  imports BUILTIN-HOOKS
  imports K-IO
  imports TCP-HOOKS
  imports #K-PARSER-INTERFACE
  imports #K-PRINTER-INTERFACE

// B, N, and P are really supposed to be Nat

  rule #open(S:String) => #open(S:String, "rw")
  rule #open(S:String, Mode:String) => #string2Int(#tcpRequest("open\x01" +String S +String "\x01" +String Mode +String "\x01")<:TCPAnswer) when Mode ==String "r" orBool Mode ==String "w" orBool Mode ==String "rw"

  rule #close(N:Int)
      => String2DotK((#tcpRequest("close\x01" +String Int2String(N) +String "\x01"))<:TCPAnswer)

  syntax K ::= String2DotK(TCPAnswer)  [function]
  rule String2DotK(S:String) => #ioError(#retrieveTCPError(S)) when #isTCPError(S)
  rule String2DotK(S:String) => .K when notBool(#isTCPError(S))
  rule String2DotK(E:TCPError) => E

  syntax Bool ::= String2Bool(TCPAnswer) [function]
  rule String2Bool("0") => false
  rule String2Bool("false") => false
  rule String2Bool("1") => true
  rule String2Bool("true") => true

  rule #tell(N:Int) => #string2Int((#tcpRequest("position\x01" +String Int2String(N) +String "\x01"))<:TCPAnswer)

  rule #seek(N:Int,P:Int)
      => String2DotK((#tcpRequest("seek\x01" +String Int2String(N) +String "\x01"
                              +String Int2String(P) +String "\x01"))<:TCPAnswer)


  rule #getc(N:Int)
      => #string2Int(#tcpRequest("readbyte\x01" +String Int2String(N) +String "\x01")) when N =/=Int 1 andBool N =/=Int 2

  rule #read(N:Int, NumBytes:Int)
      => #tcpRequest("readbytes\x01" +String Int2String(N) +String "\x01" +String Int2String(NumBytes) +String "\x01") when N =/=Int 1 andBool N =/=Int 2

  syntax K ::= "#string2Int" "(" K ")"   [function, klabel(#string2Int)]

  rule #string2Int(S:String) => String2Int(S) when lengthString(S) >=Int 0
  rule #string2Int(E:TCPError) => E

  rule #putc(N:Int,B:Int)
    => String2DotK((#tcpRequest("writebyte\x01" +String Int2String(N) +String "\x01"
                              +String Int2String(B) +String "\x01"))<:TCPAnswer) when B >=Int 0 andBool B <Int 256 andBool N =/=Int 0

  rule #write(N:Int,S:String)
    => String2DotK((#tcpRequest("writebytes\x01" +String Int2String(N) +String "\x01"
                              +String S +String "\x01"))<:TCPAnswer) when N =/=Int 0

  rule #stat(S:String)
    => #statTypes(#string2klist(#tcpRequest("stat\x01" +String S +String "\x01true\x01")<:TCPAnswer))

  rule #lstat(S:String)
    => #statTypes(#string2klist((#tcpRequest("stat\x01" +String S +String "\x01false\x01"))<:TCPAnswer))

  rule #opendir(S:String) => #string2klist((#tcpRequest("opendir\x01" +String S +String "\x01"))<:TCPAnswer)

  syntax KList ::= #string2klist(String) [function]
  rule #string2klist(S:String) => substrString(S, 0, findString(S, "\x01", 0)) ,, #string2klist(substrString(S, findString(S, "\x01", 0) +Int 1, lengthString(S))) when findString(S, "\x01", 0) =/=Int -1
  rule #string2klist(S:String) => S when findString(S, "\x01", 0) ==Int -1
  rule #string2klist(K:K) => K when isString(K) =/=K true

  syntax KList ::= #statTypes(KList) [function]
  rule #statTypes(S1:String,,S2:String,,S3:String,,S4:String,,S5:String,,S6:String,,S7:String,,S8:String,,S9:String,,S10:String,,S11:String,,S12:String) => String2Int(S1),,String2Int(S2),,String2Int(S3),,String2Bool(S4),,String2Bool(S5),,String2Bool(S6),,String2Int(S7),,String2Int(S8),,String2Int(S9),,String2Int(S10),,String2Int(S11),,String2Int(S12)
  rule #statTypes(K:K) => K

// ------------------------------
// Dynamic parsing

  rule #parse(StringToParse:String, Sort:String) => 'String2K(#tcpRequest("parse\x01" +String Sort +String "\x01" +String StringToParse +String "\x01"))::K

  syntax K ::= String2K(String) [function, hook(#K-PARSER:string2k)]
  syntax Bag ::= String2Bag(String) [function, hook(#K-PARSER:string2bag)]
  syntax String ::= K2String(K) [function, hook(#K-PRINTER:k2string)]
                  | Bag2String(Bag) [function, hook(#K-PRINTER:bag2string)]

  rule 'String2K(#noparse) => #noparse [simplification]

// ------------------------------
// System

  rule #system(Cmd:String) => #systemTypes(#string2klist(#tcpRequest("system\x01" +String Cmd +String "\x01")<:TCPAnswer))
  syntax KItem ::= #systemTypes(KList) [function]
  rule #systemTypes(ExitCode:String,,Stdout:String,,Stderr:String,,"#EOL") => #systemResult(String2Int(ExitCode),Stdout,Stderr)

endmodule
