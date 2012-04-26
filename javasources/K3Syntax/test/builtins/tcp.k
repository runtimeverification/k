require "string.k"
require "k-equal.k"
module TCP-HOOKS
  imports STRING-HOOKS
  imports K-EQUAL-HOOKS
  imports #TCP-INTERFACE
  syntax TCPAnswer ::= "#EOF" | String | "#tcpError" "(" String ")"
  rule 'isKResult(#EOF) => true [function, anywhere]

  syntax TCPAnswer ::= "#tcpRequest" "(" String ")"   [function, klabel(#tcpRequest)]
  rule #tcpRequest(S:String) => #checkTCPAnswer(##tcpRequest(S)) [function, anywhere]

  syntax TCPAnswer ::= "#checkTCPAnswer" "(" String ")"   [function, klabel(#checkTCPAnswer)]
  rule #checkTCPAnswer(S:String) 
      => #if #isTCPError(S) #then #tcpError(#retrieveTCPError(S)) #else S #fi [function, anywhere]

  rule #tcpError("EOF") => #EOF [function, anywhere]

  syntax String ::= "##tcpRequest" "(" String ")"        [function, klabel(##tcpRequest), hook(#TCP:#tcpRequest)]
                  | "#retrieveTCPError" "(" String ")"   [function, klabel(#retrieveTCPError), hook(#TCP:#retrieveTCPError)]
  syntax Bool ::= "#isTCPError" "(" String ")"           [function, klabel(#isTCPError), hook(#TCP:#isTCPError)]

endmodule
