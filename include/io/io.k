require "io/uris.k"
require "builtins/list.k"

module IO
  imports LIST
  imports URIS


  rule MyListItem(#ostream(_)) 
       MyListItem(#buffer(Buffer:String => Buffer +String Float2String(F))) 
       (MyListItem(F:Float) => .MyList) _:MyList [stdout, stderr]
  rule MyListItem(#ostream(_)) 
       MyListItem(#buffer(Buffer:String => Buffer +String Int2String(I))) 
       (MyListItem(I:Int) => .MyList) _:MyList [stdout, stderr]
  rule MyListItem(#ostream(_)) 
       MyListItem(#buffer(Buffer:String => Buffer +String S)) 
       (MyListItem(S:String) => .MyList) _:MyList [stdout, stderr]
  rule MyListItem(#buffer(Buffer:String => Buffer +String Float2String(F))) 
       (MyListItem(F:Float) => .MyList) _:MyList [stdout, stderr]
  rule MyListItem(#buffer(Buffer:String => Buffer +String Int2String(I))) 
       (MyListItem(I:Int) => .MyList) _:MyList [stdout, stderr]
  rule MyListItem(#buffer(Buffer:String => Buffer +String S)) 
       (MyListItem(S:String) => .MyList) _:MyList [stdout, stderr]

  // Send first char from the buffer to the server
  rule MyListItem(#ostream((. => #write(N, S)) ~> N:Int)) 
       MyListItem(#buffer(S:String => "")) _:MyList
    when S =/=String "" [stdout, stderr]

  // read one character at a time until we read whitespace
  rule MyListItem(#parseInput(_:KItem, Delimiters:String)) 
       MyListItem(#buffer(S:String => S +String chrChar(#getc(N)))) 
       MyListItem(#istream(N:Int)) 
    when findChar(S, Delimiters, 0) ==Int -1 [stdin]

  // when we reach whitespace, if it parses create a ListItem
  rule (MyListItem(#parseInput("String", Delimiters:String)) => MyListItem(S)) 
       MyListItem(#buffer(S:String => "")) _:MyList 
    when findChar(S, Delimiters, 0) =/=Int -1 [stdin]

  // a hack: handle the case when we read integers without the help of the IO server
//  rule (MyListItem(#parseInput("Int", Delimiters:String)) => MyListItem(String2Int(substrString(S, 0, lengthString(S) -Int 1)))) MyListItem(#buffer(S:String => "")) when findChar(S, Delimiters, 0) =/=Int -1 andBool lengthString(S) >Int 1 [stdin]

  rule (MyListItem(#parseInput(Sort:String, Delimiters:String)) 
    => MyListItem(#parse(substrString(S, 0, lengthString(S) -Int 1), Sort))) 
       MyListItem(#buffer(S:String => "")) 
       MyListItem(#istream(_)) 
    when findChar(S, Delimiters, 0) =/=Int -1 
       andBool Sort =/=String "String" 
       andBool lengthString(S) >Int 1 [stdin]

  rule MyListItem(#parseInput(Sort:String, Delimiters:String)) 
       MyListItem(#buffer(S:String => substrString(S, 1, lengthString(S)))) 
       _:MyList 
    when findChar(S, Delimiters, 0) =/=Int -1 
       andBool Sort =/=String "String" 
       andBool lengthString(S) <=Int 1 [stdin]
  
  rule MyListItem(#buffer(_)) 
       (MyListItem(#noIO) MyListItem(#istream(_:Int)) => .MyList) [stdin]

  rule (MyListItem(#ostream(_:Int)) MyListItem(#noIO) => .MyList) 
       MyListItem(#buffer(_)) [stdout, stderr]

endmodule
