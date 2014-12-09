// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/string.k"
require "builtins/list.k"

module K-IO
  imports LIST
  imports STRING-HOOKS

  syntax IOError ::= "#EOF" | "#noparse" | "#ENOENT" | "#ENOTDIR" | "#EACCES" | "#ELOOP" | "#ENAMETOOLONG" | "#EBADF" | "#ESPIPE" | "#EISDIR" | "#EINVAL"

  // B, N, and P are really supposed to be Nat
  syntax KItem ::= "#open" "(" String ")" [function]
                 | "#open" "(" String "," String ")" [function, hook(#IO:#open), impure]
                 | "#tell" "(" Int ")" [function, hook(#IO:#tell), impure]
                 | "#getc" "(" Int ")"             [function, hook(#IO:#getc), impure]
                 | "#read" "(" Int "," Int ")"    [function, hook(#IO:#read), impure]

  syntax K ::= "#close" "(" Int ")" [function, hook(#IO:#close), impure]
             | "#seek" "(" Int "," Int ")" [function, hook(#IO:#seek), impure]
             | "#putc" "(" Int "," Int ")"      [function, hook(#IO:#putc), impure]
             | "#write" "(" Int "," String ")" [function, hook(#IO:#write), impure]

  syntax KItem ::= "#ioError" "(" String ")"

  syntax KList ::= "#stat" "(" String ")" [function, hook(#IO:#stat), impure]
                 | "#lstat" "(" String ")" [function, hook(#IO:#lstat), impure]
                 | "#opendir" "(" String ")" [function, hook(#IO:#opendir), impure]

  syntax KItem ::= "#parse" "(" String "," String ")" [function, klabel(#parse), hook(#K-PARSER:#parse), impure]
  syntax KItem ::= #parseInModule(String, // input
                                  String, // start symbol
                                  String) // module name
                                  [function, hook(#K-PARSER:#parseInModule), impure]

  rule #open(S:String) => #open(S:String, "rw")

  syntax Int ::= "#stdin"   [function]
                | "#stdout" [function]
                | "#stderr" [function]

  syntax Stream ::= #parseInput(String, String)
  syntax Stream ::= #buffer(K)
  syntax Stream ::= #istream(Int)
                  | #ostream(Int)
  syntax Stream ::= "#noIO"

  rule ListItem(#ostream(_))
       ListItem(#buffer(Buffer:String => Buffer +String Float2String(F)))
       (ListItem(F:Float) => .List)
       _:List [stdout, stderr]
  rule ListItem(#ostream(_))
       ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       (ListItem(I:Int) => .List)
       _:List [stdout, stderr]
  rule ListItem(#ostream(_))
       ListItem(#buffer(Buffer:String => Buffer +String S))
       (ListItem(S:String) => .List)
       _:List [stdout, stderr]

  rule ListItem(#buffer(Buffer:String => Buffer +String Float2String(F)))
       (ListItem(F:Float) => .List)
       _:List [stdout, stderr]
  rule ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       (ListItem(I:Int) => .List)
       _:List [stdout, stderr]
  rule ListItem(#buffer(Buffer:String => Buffer +String S))
       (ListItem(S:String) => .List)
       _:List [stdout, stderr]


  // Send first char from the buffer to the server
  rule ListItem(#ostream((.K => #write(N, S)) ~> N:Int))
       ListItem(#buffer(S:String => ""))
       _:List
    when S =/=String "" [stdout, stderr]

  // read one character at a time until we read whitespace
  rule ListItem(#parseInput(_:KItem, Delimiters:String))
       ListItem(#buffer(S:String => S +String chrChar(#getc(N))))
       ListItem(#istream(N:Int))
    when findChar(S, Delimiters, 0) ==Int -1 [stdin]

  // when we reach whitespace, if it parses create a ListItem
  rule (ListItem(#parseInput("String", Delimiters:String)) => ListItem(S))
       ListItem(#buffer(S:String => ""))
       _:List
    when findChar(S, Delimiters, 0) =/=Int -1 [stdin]

  // a hack: handle the case when we read integers without the help of the IO server
  rule (ListItem(#parseInput("Int", Delimiters:String))
       => ListItem(String2Int(substrString(S, 0, lengthString(S) -Int 1))))
       ListItem(#buffer(S:String => ""))
    when findChar(S, Delimiters, 0) =/=Int -1
       andBool lengthString(S) >Int 1 [stdin]

  rule (ListItem(#parseInput(Sort:String, Delimiters:String))
       => ListItem(#parse(substrString(S, 0, lengthString(S) -Int 1), Sort)))
       ListItem(#buffer(S:String => ""))
       ListItem(#istream(_))
    when findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort =/=String "String"
       andBool lengthString(S) >Int 1 [stdin]

  rule ListItem(#parseInput(Sort:String, Delimiters:String))
       ListItem(#buffer(S:String => substrString(S, 1, lengthString(S))))
       _:List
    when findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort =/=String "String"
       andBool lengthString(S) <=Int 1 [stdin]

  rule ListItem(#buffer(_))
       (ListItem(#noIO) ListItem(#istream(_:Int)) => .List) [stdin]

  rule (ListItem(#ostream(_:Int)) ListItem(#noIO) => .List)
       ListItem(#buffer(_))
       _:List [stdout, stderr]

  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

// ------------------------------
// System

  syntax KItem ::= "#system" "(" String ")" [function, klabel(#system), hook(#IO:#system), impure]
                 | "#systemResult" "(" Int /* exit code */ "," String /* stdout */ "," String /* stderr */ ")"

endmodule
