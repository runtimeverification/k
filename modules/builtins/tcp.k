require string
require k-equal
module TCP-HOOKS
  imports STRING-HOOKS
  imports K-EQUAL-HOOKS
  syntax TCPAnswer ::= "#EOF" | String | "#tcpError" "(" String ")"
  define 'isKResult(#EOF) => true 

  syntax TCPAnswer ::= "#tcpRequest" "(" String ")"   [function klabel(#tcpRequest)]
  define #tcpRequest(S:String) => #checkTCPAnswer(##tcpRequest(S))

  syntax TCPAnswer ::= "#checkTCPAnswer" "(" String ")"   [function klabel(#checkTCPAnswer)]
  define #checkTCPAnswer(S:String) 
      => #if #isTCPError(S) #then #tcpError(#retrieveTCPError(S)) #else S #fi

  define #tcpError("EOF") => #EOF

  syntax String ::= "##tcpRequest" "(" String ")"        [function klabel(##tcpRequest) hook(#TCP:#tcpRequest)]
                  | "#retrieveTCPError" "(" String ")"   [function klabel(#retrieveTCPError) hook(#TCP:#retrieveTCPError)]
  syntax Bool ::= "#isTCPError" "(" String ")"           [function klabel(#isTCPError) hook(#TCP:#isTCPError)]

end module
