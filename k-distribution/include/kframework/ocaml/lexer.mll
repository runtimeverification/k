{
  open Parser
  open Constants.K
  open Constants
  open Prelude
}

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

module Dynarray = struct
  type 'a t = { mutable size: int;
             mutable arr: 'a array;
             default: 'a }
  let empty default = { size=0; arr=Array.make 10 default; default=default }
  let length arr = arr.size
  let get arr idx = Array.get arr.arr idx
  let add arr str = 
    let idx = arr.size in
    arr.size <- idx + 1;
    (if idx = Array.length arr.arr then
      let new_arr = Array.make (idx * 2) arr.default in
      Array.blit arr.arr 0 new_arr 0 idx;
      arr.arr <- new_arr
    else ());
    Array.set arr.arr idx str
end

type 'a dynarray = 'a Dynarray.t

let parse_k (str: string) =
  let lexbuf = Lexing.from_string str in Parser.top token lexbuf

let parse_k_file (file: string) =
  let lexbuf = Lexing.from_channel (open_in file) in Parser.top token lexbuf

let rec parse_k_binary_stack (stack: k Stack.t) (arity: int) (result: k list) : k list =
  match arity with
    0 -> result
  | _ -> parse_k_binary_stack stack (arity - 1) ((Stack.pop stack) :: result)

let parse_k_binary_int (s: char Stream.t) : int =
  let one = Char.code (Stream.next s) in
  let two = Char.code (Stream.next s) in
  let three = Char.code (Stream.next s) in
  let four = Char.code (Stream.next s) in
  (((((one * 256) + two) * 256) + three) * 256) + four

let parse_k_binary_string (s: char Stream.t) (interns: string dynarray) : string =
  let idx_in_interns = parse_k_binary_int s in
  if idx_in_interns = 0 then
    let len = parse_k_binary_int s in
    let bytes = Bytes.create len in
    for i = 0 to len - 1 do
      ignore(Stream.next s);
      Bytes.set bytes i (Stream.next s)
    done;
    let str = Bytes.to_string bytes in
    Dynarray.add interns str;
    str
  else
    Dynarray.get interns ((Dynarray.length interns) - idx_in_interns)

let rec parse_k_binary_term (module Def: Plugin.Definition) (s: char Stream.t) (stack: k Stack.t) (interns: string dynarray) (k_interns: k dynarray) : k =
  match Char.code (Stream.next s) with
| 1 -> (* ktoken *)
  let str = parse_k_binary_string s interns in
  let sort = parse_k_binary_string s interns in
  Stack.push [ktoken(parse_sort sort)(str)] stack;
  Dynarray.add k_interns (Stack.top stack);
  parse_k_binary_term (module Def) s stack interns k_interns
| 2 -> (* kapply *)
  let lbl = parse_k_binary_string s interns in
  ignore(Stream.next s);
  let arity = parse_k_binary_int s in
  let items = parse_k_binary_stack stack arity [] in
  Stack.push (if !Prelude.no_parse_eval then [Constants.denormalize (KApply((parse_klabel lbl), items))] else Def.eval (KApply((parse_klabel lbl), items)) []) stack;
  Dynarray.add k_interns (Stack.top stack);
  parse_k_binary_term (module Def) s stack interns k_interns
| 3 -> (* ksequence *)
  let arity = parse_k_binary_int s in
  let items = parse_k_binary_stack stack arity [] in
  Stack.push (List.flatten items) stack;
  Dynarray.add k_interns (Stack.top stack);
  parse_k_binary_term (module Def) s stack interns k_interns
| 4 -> (* kvariable *)
  failwith "Unsupported: Variables in subject"
| 5 -> (* krewrite *)
  failwith "Unsupported: rewrites in subject"
| 6 -> (* injectedklabel *)
  let lbl = parse_k_binary_string s interns in
  ignore(Stream.next s);
  Stack.push [InjectedKLabel (parse_klabel lbl)] stack;
  Dynarray.add k_interns (Stack.top stack);
  parse_k_binary_term (module Def) s stack interns k_interns
| 7 -> (* end *)
  Stack.pop stack
| 8 -> (* back reference *)
  let idx = parse_k_binary_int s in
  Stack.push (Dynarray.get k_interns ((Dynarray.length k_interns) - idx)) stack;
  Dynarray.add k_interns (Stack.top stack);
  parse_k_binary_term (module Def) s stack interns k_interns
| _ -> failwith "Unexpected term code in binary KAST"
 
let parse_k_binary (s: char Stream.t) : k = 
  if Stream.npeek 5 s <> ['\x7f'; 'K'; 'A'; 'S'; 'T'] then failwith "Invalid binary KAST" else
  for _ = 1 to 5 do Stream.junk s done;
  if Stream.npeek 3 s <> ['\x04'; '\x00'; '\x01'] && Stream.npeek 3 s <> ['\x04'; '\x00'; '\x00'] then failwith "Unsupported KAST version" else
  for _ = 1 to 3 do Stream.junk s done;
  parse_k_binary_term (Plugin.get ()) s (Stack.create ()) (Dynarray.empty "") (Dynarray.empty [Bottom])

let parse_k_binary_string (s: string) : k =
  parse_k_binary (Stream.of_string s)

let parse_k_binary_file (s: string) : k =
  let channel = open_in_bin s in
  let res = parse_k_binary (Stream.of_channel channel) in
  close_in channel;
  res
}
