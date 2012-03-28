require /modules/builtins/string
module TCP-HOOKS
  imports STRING-HOOKS
  syntax TCPAnswer ::= "#EOF" | String | "#tcpError" "(" String ")"
  define 'isKResult(#EOF) => true 

  declare #tcpRequest : String -> TCPAnswer 
  define #tcpRequest(S:String) => #checkTCPAnswer(##tcpRequest(S))

  declare #checkTCPAnswer : String -> TCPAnswer
  define #checkTCPAnswer(S:String) 
      => #EOF when #isTCPError(S) andBool "EOF" ==String #retrieveTCPError(S) 

  declare ##tcpRequest : String -> String [hook(#TCP:#tcpRequest)]
  declare #isTCPError : String -> Bool [hook(#TCP:#isTCPError)]
  declare #retrieveTCPError : String -> String [hook(#TCP:#retrieveTCPError)]
end module
