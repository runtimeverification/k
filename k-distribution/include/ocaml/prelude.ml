open Constants

module KMap = Map.Make(K)
module KSet = Set.Make(K)

open Constants.K
type k = K.t

(* this is needed so that statically linked binary will contain this module that is needed by dynamically linked realdef *)
let _ = Gc.stat

exception Stuck of k
exception Not_implemented

let interned_bottom = [Bottom]

module MemoKey = struct
  type t = k list
  let compare c1 c2 = compare_klist c1 c2
end

module Memo = Map.Make(MemoKey)

module KIdentityHash = struct
  type t = k
  let equal = equal_k
  let hash = Hashtbl.hash_param 1000 1000
end

type step_function = StepFunc of (k -> (k * step_function))

module KIdentityHashtbl = Hashtbl.Make(KIdentityHash)

module KMemoIdentityHash = struct
  type t = k
  let equal = equal_k
  let hash = hash_k_param 900
end

module KMemoIdentityHashtbl = Hashtbl.Make(KMemoIdentityHash)

module GuardElt = struct
  type t = Guard of int
  let compare c1 c2 = match c1 with Guard(i1) -> match c2 with Guard(i2) -> i2 - i1
end
module Guard = Set.Make(GuardElt)
let freshCounter : Z.t ref = ref Z.zero
let isTrue(c: k) : bool = match c with
| ([(Bool true)]) -> true
| _ -> false
let rec list_range (c: k list * int * int) : k list = match c with
| (_, 0, 0) -> []
| (head :: tail, 0, len) -> head :: list_range(tail, 0, len - 1)
| (_ :: tail, n, len) -> list_range(tail, n - 1, len)
| ([], _, _) -> raise(Failure "list_range")
let float_to_string (f: Gmp.FR.t) : string = if Gmp.FR.is_nan f then "NaN" else if Gmp.FR.is_inf f then if Gmp.FR.sgn f > 0 then "Infinity" else "-Infinity" else Gmp.FR.to_string_base_digits Gmp.GMP_RNDN 10 0 f
let precise_float_to_string (f,p,e) = float_to_string(f) ^ "p" ^ string_of_int p ^ "x" ^ string_of_int e
let k_of_list lbl l = match l with
  [] -> denormalize (KApply((unit_for lbl),[]))
| hd :: tl -> List.fold_left (fun list el -> denormalize (KApply(lbl, [list] :: [denormalize (KApply((el_for lbl),[el]))] :: []))) (denormalize (KApply((el_for lbl),[hd]))) tl
let k_of_set lbl s = if (KSet.cardinal s) = 0 then denormalize (KApply((unit_for lbl),[])) else
  let hd = KSet.choose s in KSet.fold (fun el set -> denormalize (KApply(lbl, [set] :: [denormalize (KApply((el_for lbl),[el]))] :: []))) (KSet.remove hd s) (denormalize (KApply((el_for lbl),[hd])))
let k_of_map lbl m = if (KMap.cardinal m) = 0 then denormalize (KApply((unit_for lbl),[])) else
  let (k,v) = KMap.choose m in KMap.fold (fun k v map -> denormalize (KApply(lbl, [map] :: [denormalize (val_for lbl k v)] :: []))) (KMap.remove k m) (denormalize (val_for lbl k v))
let k_of_array sort a = let uuid = Uuidm.create `V4 in
  fst (Dynarray.fold_left (fun (res,i) elt -> match elt with [Bottom] -> res,(Z.add i Z.one) | _ -> (denormalize(KApply((el_for_array sort),[[res]; [Int i]; elt]))),(Z.add i Z.one)) ((denormalize(KApply((unit_for_array sort), [[String (Uuidm.to_string uuid)]; [Int (Z.of_int (Dynarray.length a))]]))),Z.zero) a)
let k_char_escape (buf: Buffer.t) (c: char) : unit = match c with
| '"' -> Buffer.add_string buf "\\\""
| '\\' -> Buffer.add_string buf "\\\\"
| '\n' -> Buffer.add_string buf "\\n"
| '\t' -> Buffer.add_string buf "\\t"
| '\r' -> Buffer.add_string buf "\\r"
| _ when let code = Char.code c in code >= 32 && code < 127 -> Buffer.add_char buf c
| _ -> Buffer.add_string buf (Printf.sprintf "\\x%02x" (Char.code c))
let k_string_escape str =
  let buf = Buffer.create (String.length str) in
  String.iter (k_char_escape buf) str; Buffer.contents buf
let print_k_binary (c: k) : string =  let buf = Buffer.create 16 in
  let ktoken_code = "\x01" in
  let kapply_code = "\x02" in
  let ksequence_code = "\x03" in
  let injectedklabel_code = "\x06" in
  let end_code = "\x07" in
  let backreference_code = "\x08" in
  let table_size = (1 lsl 18) in
  let intern = Hashtbl.create 16 in
  let k_intern = KIdentityHashtbl.create table_size in
  let terms_visited = ref 0 in
  let print_int (i: int) : unit =
    let one = (i lsr 24) land 0xff in
    let two = (i lsr 16) land 0xff in
    let three = (i lsr 8) land 0xff in
    let four = (i lsr 0) land 0xff in
    Buffer.add_char buf (Char.chr one);
    Buffer.add_char buf (Char.chr two);
    Buffer.add_char buf (Char.chr three);
    Buffer.add_char buf (Char.chr four) in
  let print_string (s: string) : unit =
    let idx = try Hashtbl.find intern s with Not_found -> Hashtbl.length intern in
    print_int (Hashtbl.length intern - idx);
    if idx = Hashtbl.length intern then
      (print_int (String.length s);
      for i = 0 to (String.length s) - 1 do
        Buffer.add_char buf '\x00';
        Buffer.add_char buf (String.get s i)
      done;
      let new_idx = (Hashtbl.length intern) in
      assert (not (Hashtbl.mem intern s));
      Hashtbl.add intern s new_idx)
    else () in
  let add_intern (c: k) : unit =
    KIdentityHashtbl.replace k_intern c !terms_visited;
    terms_visited := !terms_visited + 1;
    if !terms_visited land (table_size - 1) = 0 then KIdentityHashtbl.clear k_intern else () in
  let rec print_klist(c: k list) : unit = match c with
  | [] -> ()
  | e::l  -> print_k e 0; print_klist l
  and print_k(c: k) (size: int) : unit = match c with
  | [] -> if size <> 1 then (Buffer.add_string buf ksequence_code; add_intern c; print_int size) else ()
  | e::l -> print_kitem(normalize e, [e]); print_k l (size + 1)
  and print_kitem = function (c, as_k) ->
  if KIdentityHashtbl.mem k_intern as_k then
    (Buffer.add_string buf backreference_code; print_int (!terms_visited - (KIdentityHashtbl.find k_intern as_k)); add_intern as_k)
  else match c with
  | KApply(klabel, klist) -> print_klist klist; Buffer.add_string buf kapply_code; add_intern as_k; print_string (print_klabel_string klabel); Buffer.add_char buf '\x00'; print_int (List.length klist)
  | KItem (KToken(sort, s)) -> Buffer.add_string buf ktoken_code; add_intern as_k; print_string s; print_string (print_sort sort)
  | KItem (InjectedKLabel(klabel)) -> Buffer.add_string buf injectedklabel_code; add_intern as_k; print_string (print_klabel_string klabel); Buffer.add_char buf '\x00'
  | KItem (Bool(b)) -> print_kitem(KItem (KToken(SortBool, string_of_bool(b))), [Bool b])
  | KItem (String(s)) -> print_kitem(KItem (KToken(SortString, "\"" ^ (k_string_escape s) ^ "\"")), [String s])
  | KItem (Bytes(b)) -> print_kitem(KItem (KToken(SortBytes, "b\"" ^ (k_string_escape (Bytes.to_string b)) ^ "\"")), [Bytes b])
  | KItem (StringBuffer(s)) -> print_kitem(KItem (KToken(SortStringBuffer, "\"" ^ (k_string_escape (Buffer.contents s)) ^ "\"")), [StringBuffer s])
  | KItem (Int(i)) -> print_kitem(KItem (KToken(SortInt, Z.to_string(i))), [Int i])
  | KItem (Float(f,e,p)) -> print_kitem(KItem (KToken(SortFloat, precise_float_to_string(f,p,e))), [Float(f,e,p)])
  | KItem (Bottom) -> print_kitem(KApply(Lbl'Hash'Bottom, []), interned_bottom)
  | KItem (List(sort,lbl,l)) -> print_kitem(normalize (k_of_list lbl l), [List(sort,lbl,l)])
  | KItem (Set(sort,lbl,s)) -> print_kitem(normalize (k_of_set lbl s), [Set(sort,lbl,s)])
  | KItem (Map(sort,lbl,m)) -> print_kitem(normalize (k_of_map lbl m), [Map(sort,lbl,m)])
  | KItem (Array(sort,d,a)) -> print_kitem(normalize (k_of_array sort a), [Array(sort,d,a)])
  | KItem (ThreadLocal) -> print_kitem(KApply(Lbl'Hash'ThreadLocal, []), [ThreadLocal])
  | KItem (Thread(k1,k2,k3,k4)) -> print_kitem(KApply(Lbl'Hash'Thread, [k1; k2; k3; k4]), [Thread(k1,k2,k3,k4)])
  | KItem _ -> invalid_arg "print_kitem"
  in Buffer.add_string buf "\x7fKAST\x04\x00\x01"; print_k c 0; Buffer.add_string buf end_code;
  Buffer.contents buf

let print_k (c: k) : string = let buf = Buffer.create 16 in
  let rec print_klist(c: k list) : unit = match c with
  | [] -> Buffer.add_string buf ".KList"
  | e::[] -> print_k(e)
  | e1::e2::l -> print_k(e1); Buffer.add_string buf ", "; print_klist(e2::l)
  and print_k(c: k) : unit = match c with
  | [] -> Buffer.add_string buf ".K"
  | e::[] -> print_kitem(normalize e)
  | e1::e2::l -> print_kitem(normalize e1); Buffer.add_string buf " ~> "; print_k(e2::l)
  and print_kitem(c: normal_kitem) : unit = match c with
  | KApply(klabel, klist) -> Buffer.add_string buf (print_klabel klabel); Buffer.add_char buf '('; print_klist(klist); Buffer.add_char buf ')'
  | KItem (KToken(sort, s)) -> Buffer.add_string buf "#token(\""; Buffer.add_string buf (k_string_escape s);
        Buffer.add_string buf "\", \""; Buffer.add_string buf (print_sort sort); Buffer.add_string buf "\")"
  | KItem (InjectedKLabel(klabel)) -> Buffer.add_string buf "#klabel("; Buffer.add_string buf (print_klabel klabel); Buffer.add_char buf ')'
  | KItem (Bool(b)) -> print_kitem(KItem (KToken(SortBool, string_of_bool(b))))
  | KItem (String(s)) -> print_kitem(KItem (KToken(SortString, "\"" ^ (k_string_escape s) ^ "\"")))
  | KItem (Bytes(b)) -> print_kitem(KItem (KToken(SortBytes, "b\"" ^ (k_string_escape (Bytes.to_string b)) ^ "\"")))
  | KItem (StringBuffer(s)) -> print_kitem(KItem (KToken(SortStringBuffer, "\"" ^ (k_string_escape (Buffer.contents s)) ^ "\"")))
  | KItem (Int(i)) -> print_kitem(KItem (KToken(SortInt, Z.to_string(i))))
  | KItem (Float(f,e,p)) -> print_kitem(KItem (KToken(SortFloat, precise_float_to_string(f,p,e))))
  | KItem (Bottom) -> print_kitem(KApply(Lbl'Hash'Bottom, []))
  | KItem (List(_,lbl,l)) -> print_kitem(normalize (k_of_list lbl l))
  | KItem (Set(_,lbl,s)) -> print_kitem(normalize (k_of_set lbl s))
  | KItem (Map(_,lbl,m)) -> print_kitem(normalize (k_of_map lbl m))
  | KItem (Array(sort,_,a)) -> print_kitem(normalize (k_of_array sort a))
  | KItem (ThreadLocal) -> print_kitem(KApply(Lbl'Hash'ThreadLocal, []))
  | KItem (Thread(k1, k2, k3, k4)) -> print_kitem(KApply(Lbl'Hash'Thread, [k1; k2; k3; k4]))
  | KItem _ -> invalid_arg "non-normal kitem"
  in print_k c; Buffer.contents buf
module Subst = Map.Make(String)
let print_subst (out: out_channel) (c: k Subst.t) : unit =
  output_string out "1\n"; Subst.iter (fun v k -> output_string out (v ^ "\n" ^ (print_k k) ^ "\n")) c
let print_subst_binary (out: out_channel) (c: k Subst.t) : unit =
  output_binary_int out 1; Subst.iter (fun v k -> output_binary_int out (String.length v); output_string out v; output_string out (print_k_binary k)) c
let emin (exp: int) (prec: int) : int = (- (1 lsl (exp - 1))) + 4 - prec
let emin_normal (exp: int) : int = (- (1 lsl (exp - 1))) + 2
let emax (exp: int) : int = 1 lsl (exp - 1)
let round_to_range (c: kitem) : kitem = match c with
    Float(f,e,p) -> let (cr, t) = (Gmp.FR.check_range p Gmp.GMP_RNDN (emin e p) (emax e) f) in Float((Gmp.FR.subnormalize cr t Gmp.GMP_RNDN),e,p)
  | _ -> raise (Invalid_argument "round_to_range")
let curr_fd : Z.t ref = ref (Z.of_int 3)
let file_descriptors = let m = Hashtbl.create 5 in Hashtbl.add m (Z.of_int 0) Unix.stdin; Hashtbl.add m (Z.of_int 1) Unix.stdout; Hashtbl.add m (Z.of_int 2) Unix.stderr; m
let default_file_perm = 0o777
let convert_open_flags (s: string) : Unix.open_flag list =
  match s with
      "r" -> [Unix.O_RDONLY]
    | "w" -> [Unix.O_WRONLY; Unix.O_TRUNC; Unix.O_CREAT]
    | "wx" -> [Unix.O_WRONLY; Unix.O_EXCL; Unix.O_CREAT]
    | "a" -> [Unix.O_WRONLY; Unix.O_APPEND; Unix.O_CREAT]
    | "rb" -> [Unix.O_RDONLY]
    | "wb" -> [Unix.O_WRONLY; Unix.O_TRUNC; Unix.O_CREAT]
    | "wbx" -> [Unix.O_WRONLY; Unix.O_EXCL; Unix.O_CREAT]
    | "ab" -> [Unix.O_WRONLY; Unix.O_APPEND; Unix.O_CREAT]
    | "r+" -> [Unix.O_RDWR]
    | "w+" -> [Unix.O_RDWR; Unix.O_TRUNC; Unix.O_CREAT]
    | "w+x" -> [Unix.O_RDWR; Unix.O_EXCL; Unix.O_CREAT]
    | "a+" -> [Unix.O_RDWR; Unix.O_APPEND; Unix.O_CREAT]
    | "r+b" | "rb+" -> [Unix.O_RDWR]
    | "w+b" | "wb+" -> [Unix.O_RDWR; Unix.O_TRUNC; Unix.O_CREAT]
    | "w+bx" | "wb+x" -> [Unix.O_RDWR; Unix.O_EXCL; Unix.O_CREAT]
    | "a+b" | "ab+" -> [Unix.O_RDWR; Unix.O_APPEND; Unix.O_CREAT]
    | _ -> raise (Invalid_argument "convert_open_flags")
let unix_error (f: unit -> k) = try f () with Unix.Unix_error(err,_,_) -> match err with
| Unix.EUNKNOWNERR(i) -> [KApply1((parse_klabel "#unknownIOError"), [Int (Z.of_int i)])]
| _ -> [KApply0(parse_klabel(match err with
| Unix.E2BIG -> "#E2BIG"
| Unix.EACCES -> "#EACCES"
| Unix.EAGAIN -> "#EAGAIN"
| Unix.EBADF -> "#EBADF"
| Unix.EBUSY -> "#EBUSY"
| Unix.ECHILD -> "#ECHILD"
| Unix.EDEADLK -> "#EDEADLK"
| Unix.EDOM -> "#EDOM"
| Unix.EEXIST -> "#EEXIST"
| Unix.EFAULT -> "#EFAULT"
| Unix.EFBIG -> "#EFBIG"
| Unix.EINTR -> "#EINTR"
| Unix.EINVAL -> "#EINVAL"
| Unix.EIO -> "#EIO"
| Unix.EISDIR -> "#EISDIR"
| Unix.EMFILE -> "#EMFILE"
| Unix.EMLINK -> "#EMLINK"
| Unix.ENAMETOOLONG -> "#ENAMETOOLONG"
| Unix.ENFILE -> "#ENFILE"
| Unix.ENODEV -> "#ENODEV"
| Unix.ENOENT -> "#ENOENT"
| Unix.ENOEXEC -> "#ENOEXEC"
| Unix.ENOLCK -> "#ENOLCK"
| Unix.ENOMEM -> "#ENOMEM"
| Unix.ENOSPC -> "#ENOSPC"
| Unix.ENOSYS -> "#ENOSYS"
| Unix.ENOTDIR -> "#ENOTDIR"
| Unix.ENOTEMPTY -> "#ENOTEMPTY"
| Unix.ENOTTY -> "#ENOTTY"
| Unix.ENXIO -> "#ENXIO"
| Unix.EPERM -> "#EPERM"
| Unix.EPIPE -> "#EPIPE"
| Unix.ERANGE -> "#ERANGE"
| Unix.EROFS -> "#EROFS"
| Unix.ESPIPE -> "#ESPIPE"
| Unix.ESRCH -> "#ESRCH"
| Unix.EXDEV -> "#EXDEV"
| Unix.EWOULDBLOCK -> "#EWOULDBLOCK"
| Unix.EINPROGRESS -> "#EINPROGRESS"
| Unix.EALREADY -> "#EALREADY"
| Unix.ENOTSOCK -> "#ENOTSOCK"
| Unix.EDESTADDRREQ -> "#EDESTADDRREQ"
| Unix.EMSGSIZE -> "#EMSGSIZE"
| Unix.EPROTOTYPE -> "#EPROTOTYPE"
| Unix.ENOPROTOOPT -> "#ENOPROTOOPT"
| Unix.EPROTONOSUPPORT -> "#EPROTONOSUPPORT"
| Unix.ESOCKTNOSUPPORT -> "#ESOCKTNOSUPPORT"
| Unix.EOPNOTSUPP -> "#EOPNOTSUPP"
| Unix.EPFNOSUPPORT -> "#EPFNOSUPPORT"
| Unix.EAFNOSUPPORT -> "#EAFNOSUPPORT"
| Unix.EADDRINUSE -> "#EADDRINUSE"
| Unix.EADDRNOTAVAIL -> "#EADDRNOTAVAIL"
| Unix.ENETDOWN -> "#ENETDOWN"
| Unix.ENETUNREACH -> "#ENETUNREACH"
| Unix.ENETRESET -> "#ENETRESET"
| Unix.ECONNABORTED -> "#ECONNABORTED"
| Unix.ECONNRESET -> "#ECONNRESET"
| Unix.ENOBUFS -> "#ENOBUFS"
| Unix.EISCONN -> "#EISCONN"
| Unix.ENOTCONN -> "#ENOTCONN"
| Unix.ESHUTDOWN -> "#ESHUTDOWN"
| Unix.ETOOMANYREFS -> "#ETOOMANYREFS"
| Unix.ETIMEDOUT -> "#ETIMEDOUT"
| Unix.ECONNREFUSED -> "#ECONNREFUSED"
| Unix.EHOSTDOWN -> "#EHOSTDOWN"
| Unix.EHOSTUNREACH -> "#EHOSTUNREACH"
| Unix.ELOOP -> "#ELOOP"
| Unix.EOVERFLOW -> "#EOVERFLOW"
| Unix.EUNKNOWNERR(_) -> failwith "unreachable"
))]

let to_string_base (base: int) (i: Z.t) : string = match base with
  10 -> Z.format "%d" i
| 2 -> Z.format "%b" i
| 8 -> Z.format "%o" i
| 16 -> Z.format "%x" i
| _ -> raise Not_implemented
let to_zarith (i: Gmp.Z.t) : Z.t = Z.of_string (Gmp.Z.to_string i)
let from_zarith (i: Z.t) : Gmp.Z.t = Gmp.Z.from_string (Z.to_string i)

let deconstruct_float (f: Gmp.FR.t) (prec: int) (e: int) : bool * int * Z.t option =
 let (digits, exp) = Gmp.FR.to_string_exp_base_digits Gmp.GMP_RNDN 2 prec f in match digits with
 | "@Inf@" -> false, (emax e), Some Z.zero
 | "-@Inf@" -> true, (emax e), Some Z.zero
 | "@NaN@" -> false, (emax e), None
 | "-@NaN@" -> true, (emax e), None
 | _ -> let min_exp = emin_normal e in
 let significand = Z.abs (Z.of_string_base 2 digits) in
 let scaled_significand = if exp < min_exp then
   (Z.shift_right significand (min_exp - (exp - 1))) else
   significand in
 let true_exp = if exp < min_exp then min_exp else if exp > (emax e) then emax e else (exp - 1) in
 (String.get digits 0 = '-'), true_exp, Some scaled_significand

let float_regexp = Str.regexp "\\(.*\\)[pP]\\([0-9]+\\)[xX]\\([0-9]+\\)"

let unescape_k_string (str: string) =
  let str = String.sub str 1 (String.length str - 2) in
  Scanf.unescaped str

 let parse_float (str: string) : int * int * string =
   let (cMAX_FLOAT_PREC, cMAX_FLOAT_EXP) = (237, 19) in
  if Str.string_match float_regexp str 0 then
    let prec = int_of_string (Str.matched_group 2 str) in
    let exp = int_of_string (Str.matched_group 3 str) in
    (prec, exp, (Str.matched_group 1 str))
  else (cMAX_FLOAT_PREC, cMAX_FLOAT_EXP, str)

let signed_extract i idx len =
  if len = 0 then Z.zero else
  if Z.testbit i (idx + len - 1)
  then let max = Z.shift_left Z.one (len-1) in
    Z.sub (Z.extract (Z.add (Z.extract i idx len) max) 0 len) max
  else Z.extract i idx len

let reverse b =
  let len = Bytes.length b in
  let res = Bytes.create len in
  for i = 0 to len - 1 do
    Bytes.set res (len - i - 1) (Bytes.get b i)
  done;
  res

let ktoken (s: sort) (str: string) : kitem = match s with
| SortInt -> Int (Z.of_string str)
| SortFloat -> let (p,e,f) = parse_float str in (round_to_range(Float ((Gmp.FR.from_string_prec_base p Gmp.GMP_RNDN 10 f), e, p)))
| SortString -> String (unescape_k_string str)
| SortBool -> Bool (bool_of_string str)
| _ -> KToken(s,str)

let get_exit_code(subst: k Subst.t) : int = match (Subst.fold (fun _ v res -> match (v, res) with
    [Int i], None -> Some (Z.to_int i)
  | [Int _], Some _ -> failwith "Bad exit code pattern"
  | _ -> res) subst None) with Some i -> i | _ -> failwith "Bad exit code pattern"

(* set to true if you don't want the k parser to evaluate functions.
   this is used by --ocaml-compile in order to prevent us from evaluating
   argv while marshalling data. *)
let no_parse_eval = ref false

module CONFIG =
struct
  let depth = ref (-1)
  let sys_argv = ref Sys.argv
  let output_file = ref "config"

  let set_sys_argv () =
    let has_rv_args () =
      try let _ = Sys.getenv "RV_MATCH_BINARY_FLAGS" in true
      with Not_found -> false
    in if has_rv_args () then
      let cmd = ref [Sys.argv.(0)] in
      let set_depth d = depth := d in
      let set_output_file outf = output_file := outf in
      let add_sys_argv arg = cmd := arg::!cmd in
      let anon_arg a = print_endline ("Invalid argument: " ^ a ^". Will be ignored") in
      let string_of_list l = "[" ^ String.concat "; " l ^ "]" in
    begin
      print_endline "RV_MATCH_BINARY_FLAGS is set. parsing RV_Match specific args.";
      let speclist = [
        ("--depth", Arg.Int (set_depth), "The maximum number of computational steps to execute the definition for.");
        ("--output-file", Arg.String (set_output_file), "The file to store (failing) configuration into.");
        ("--", Arg.Rest (add_sys_argv), "Command line for the program");
      ]
      in let usage_msg = "Invalid RV options. Usage:\n  " ^ Sys.argv.(0) ^ " <rv-options> -- <pgm-options>\nRV options available:"
      in Arg.parse speclist anon_arg usage_msg;
      sys_argv := Array.of_list (List.rev !cmd);
      print_endline ("Max depth: " ^ string_of_int !depth);
      print_endline ("Command line: " ^ string_of_list (List.rev !cmd));
    end
  else ()
end

module RACE =
struct
  type rule_type =
    | Owise
    | Heat
    | Cool
    | Nondet
    | NoType
  let rec valid_continuations = function
    | [] -> []
    | h::t -> valid_continuation h t :: valid_continuations t
  and valid_continuation c = function
    | [] -> c
    | h::t -> valid_cont c h ; valid_continuation c t
  and valid_cont (_, (_,t1 ,l1), _) (_, (_, t2, l2), _) = match (t1,t2) with
    | (Heat, Heat)
    | (Nondet, Nondet) -> ()
    | _ -> Printf.printf "Warning: Race detected between rules at %s and %s.\n" l1 l2
  let all_steps (one_step : k -> int -> (k * (int * rule_type * string) * step_function)) (c: k) (start_after: int) : (k * (int * rule_type * string) * step_function) list =
    let rec steps start l =
      try let (_, (s, _, _), _) as r = one_step c start
          in steps s (r :: l)
      with (Stuck _) -> l
    in steps start_after []
end
