open Constants
open Constants.K
open Prelude
open Lexer

module META =
struct
  let hook_parseAST c _ _ _ _ = match c with
    | [String s] -> Lexer.parse_k s
end
