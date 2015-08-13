{ open Parser }

rule token = parse
  | [' ' '\t' '\n' '\r'] { token lexbuf }
  | "~>" { KSEQ }
  | ".::K" { DOTK }
  | ".K" { DOTK }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "," { COMMA }
  | ".::KList" { DOTKLIST }
  | ".KList" { DOTKLIST }
  | "#token" { TOKENLABEL }
  | "#klabel" { KLABELLABEL }
  | (['#' 'a'-'z'](['a'-'z' 'A'-'Z' '0'-'9'])*) as label { KLABEL label }
  | ('"' ([^'"' '\\']|('\\' _))* '"') as s { STRING (Prelude.unescape_k_string s) }
  | "`" (([^'`' '\\']|('\\' _))* as l) '`' { KLABEL (Str.global_replace (Str.regexp "\\\\(.)") "\\1" l) }
  | eof { EOF }

{ 
let parse_k (str: string) =
  let lexbuf = Lexing.from_string str in Parser.top token lexbuf
}
