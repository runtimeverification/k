require "io/io.k"

module IO-AUX

//imports AST-SYNTAX
//imports UTIL
//imports IR
//imports OUTPUT
imports URIS
imports TCP-HOOKS
imports LIST
imports IO

//configuration <k>$PGM:KItem</k><out stream="stdout">.MyList</out>
//configuration <k>$PGM:KItem</k><out stream="stdout">.List</out>

// This module requires using the Java backend to work

syntax KItem ::=
  writeToFile(String, String) [function]
| checkOpen(String, K) [function]
| writeToFileNum(String, Int, String) [function]
| checkWrite(String, Int, String, K) [function]

//context #write(HOLE, S)

// Writes the string "Content" to the file "Filename".
// The first step is to open the filename and get a file id
rule writeToFile(Filename, Content) => writeToFileNum(Filename, checkOpen(Filename, #open(Filename, "w")), Content)

// After opening the file, check that there was no error
//rule checkOpen(_, X) => X
rule checkOpen(_, X:Int) => X
//rule <k>checkOpen(Filename, X:TCPError) => X </k>
//  <out>... . => ListItem("Error opening " +String Filename +String ": " +String K2String(X))</out>
//rule <k>checkOpen(Filename, X:TCPError) => X </k><out>... (. => MyListItem("Error opening " +String Filename +String ": " +String K2String(X)))</out>

// Write the string "Content" to open file number "Num" which has name "Filename"
rule writeToFileNum(Filename, Num, Content) => #write(Num, Content) ~> #close(Num)
//rule writeToFileNum(Filename, Num, Content) => checkWrite(Filename, Num, Content, #write(Num, Content)) ~> #close(Num)
//rule checkWrite(_, _, _, X:Int) => X
//rule <k>checkWrite(Filename, _, _, X:TCPError) => X </k><out>L => L MyListItem("Error writing to " +String Filename +String ": " +String K2String(X))</out>

/*
rule <k>checkWrite(Filename, _, _, X:TCPError) => X </k><out>... . => MyListItem("Error writing to " +String Filename +String ": " +String K2String(X))</out>
*/

endmodule
