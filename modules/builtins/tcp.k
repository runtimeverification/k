require string
require k-equal
module TCP-HOOKS
  imports STRING-HOOKS
  imports K-EQUAL-HOOKS
  syntax TCPAnswer ::= "#EOF" | String | "#tcpError" "(" String ")"
  define 'isKResult(#EOF) => true 

  declare #tcpRequest : String -> TCPAnswer 
  define #tcpRequest(S:String) => #checkTCPAnswer(##tcpRequest(S))

  declare #checkTCPAnswer : String -> TCPAnswer
  define #checkTCPAnswer(S:String) 
      => #if #isTCPError(S) #then #tcpError(#retrieveTCPError(S)) #else S #fi

  define #tcpError("EOF") => #EOF

  declare ##tcpRequest : String -> String [hook(#TCP:#tcpRequest)]
  declare #isTCPError : String -> Bool [hook(#TCP:#isTCPError)]
  declare #retrieveTCPError : String -> String [hook(#TCP:#retrieveTCPError)]
end module
