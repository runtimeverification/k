require "string.k"
require "k-equal.k"
module TCP-HOOKS
  imports STRING-HOOKS
  imports K-EQUAL-HOOKS
  imports #TCP-INTERFACE
  syntax TCPAnswer ::= String | TCPError
  syntax TCPError ::= "#EOF" | "#tcpError" "(" String ")" | "#noparse" | "#ENOENT" | "#ENOTDIR" | "#EACCES" | "#ELOOP" | "#ENAMETOOLONG"
  rule isKResult(#EOF) => true [function, anywhere]

  syntax TCPAnswer ::= "#tcpRequest" "(" String ")"   [function, klabel(#tcpRequest)]
  rule #tcpRequest(S:String) => #checkTCPAnswer(##tcpRequest(S))

  syntax TCPAnswer ::= "#checkTCPAnswer" "(" String ")"   [function, klabel(#checkTCPAnswer)]
  rule #checkTCPAnswer(S:String) 
      => #if #isTCPError(S) #then #tcpError(#retrieveTCPError(S)) #else S #fi

  rule #tcpError("EOF") => #EOF [function, anywhere]
  rule #tcpError("noparse") => #noparse [function, anywhere]
  rule #tcpError("ENOENT") => #ENOENT [function, anywhere]
  rule #tcpError("ENOTDIR") => #ENOTDIR [function, anywhere]
  rule #tcpError("EACCES") => #EACCES [function, anywhere]
  rule #tcpError("ELOOP") => #ELOOP [function, anywhere]
  rule #tcpError("ENAMETOOLONG") => #ENAMETOOLONG [function, anywhere]

  syntax String ::= "##tcpRequest" "(" String ")"        [function, klabel(##tcpRequest), hook(#TCP:#tcpRequest)]
                  | "#retrieveTCPError" "(" String ")"   [function, klabel(#retrieveTCPError), hook(#TCP:#retrieveTCPError)]
  syntax Bool ::= "#isTCPError" "(" String ")"           [function, klabel(#isTCPError), hook(#TCP:#isTCPError)]

endmodule
