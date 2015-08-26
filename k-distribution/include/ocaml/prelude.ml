open Constants

module KMap = Map.Make(K)
module KSet = Set.Make(K)

open Constants.K
type k = K.t

exception Stuck of k
exception Not_implemented

module MemoKey = struct
  type t = k list
  let compare c1 c2 = compare_klist c1 c2
end

module Memo = Map.Make(MemoKey)

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
let k_of_list lbl l = match l with 
  [] -> denormalize (KApply((unit_for lbl),[]))
| hd :: tl -> List.fold_left (fun list el -> denormalize (KApply(lbl, [list] :: [denormalize (KApply((el_for lbl),[el]))] :: []))) (denormalize (KApply((el_for lbl),[hd]))) tl
let k_of_set lbl s = if (KSet.cardinal s) = 0 then denormalize (KApply((unit_for lbl),[])) else 
  let hd = KSet.choose s in KSet.fold (fun el set -> denormalize (KApply(lbl, [set] :: [denormalize (KApply((el_for lbl),[el]))] :: []))) (KSet.remove hd s) (denormalize (KApply((el_for lbl),[hd])))
let k_of_map lbl m = if (KMap.cardinal m) = 0 then denormalize (KApply((unit_for lbl),[])) else 
  let (k,v) = KMap.choose m in KMap.fold (fun k v map -> denormalize (KApply(lbl, [map] :: [denormalize (KApply((el_for lbl),[k;v]))] :: []))) (KMap.remove k m) (denormalize (KApply((el_for lbl),[k;v])))
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
  | KItem (KToken(sort, s)) -> Buffer.add_string buf "#token(\""; Buffer.add_string buf (String.escaped s); 
        Buffer.add_string buf "\", \""; Buffer.add_string buf (print_sort sort); Buffer.add_string buf "\")"
  | KItem (InjectedKLabel(klabel)) -> Buffer.add_string buf "#klabel("; Buffer.add_string buf (print_klabel klabel); Buffer.add_char buf ')'
  | KItem (Bool(b)) -> print_kitem(KItem (KToken(SortBool, string_of_bool(b))))
  | KItem (String(s)) -> print_kitem(KItem (KToken(SortString, "\"" ^ (String.escaped s) ^ "\"")))
  | KItem (Int(i)) -> print_kitem(KItem (KToken(SortInt, Z.to_string(i))))
  | KItem (Float(f,_,_)) -> print_kitem(KItem (KToken(SortFloat, float_to_string(f))))
  | KItem (Bottom) -> Buffer.add_string buf "`#Bottom`(.KList)"
  | KItem (List(_,lbl,l)) -> print_kitem(normalize (k_of_list lbl l))
  | KItem (Set(_,lbl,s)) -> print_kitem(normalize (k_of_set lbl s))
  | KItem (Map(_,lbl,m)) -> print_kitem(normalize (k_of_map lbl m))
  in print_k c; Buffer.contents buf
module Subst = Map.Make(String)
let print_subst (out: out_channel) (c: k Subst.t) : unit = 
  output_string out "1\n"; Subst.iter (fun v k -> output_string out (v ^ "\n" ^ (print_k k) ^ "\n")) c
let emin (exp: int) (prec: int) : int = (- (1 lsl (exp - 1))) + 4 - prec
let emin_normal (exp: int) : int = (- (1 lsl (exp - 1))) + 2
let emax (exp: int) : int = 1 lsl (exp - 1)
let round_to_range (c: kitem) : kitem = match c with 
    Float(f,e,p) -> let (cr, t) = (Gmp.FR.check_range p Gmp.GMP_RNDN (emin e p) (emax e) f) in Float((Gmp.FR.subnormalize cr t Gmp.GMP_RNDN),e,p)
  | _ -> raise (Invalid_argument "round_to_range")
let curr_fd : Z.t ref = ref (Z.of_int 3)
let file_descriptors = let m = Hashtbl.create 5 in Hashtbl.add m (Z.of_int 0) Unix.stdin; Hashtbl.add m (Z.of_int 1) Unix.stdout; Hashtbl.add m (Z.of_int 2) Unix.stderr; m
let default_file_perm = let v = Unix.umask 0 in let _ = Unix.umask v in (lnot v) land 0o777
let convert_open_flags (s: string) : Unix.open_flag list = 
  match s with 
      "r" -> [Unix.O_RDONLY] 
    | "w" -> [Unix.O_WRONLY] 
    | "rw" -> [Unix.O_RDWR]
    | _ -> raise (Invalid_argument "convert_open_flags")
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
 | "@Inf@" -> false, (emax exp), Some Z.zero
 | "-@Inf@" -> true, (emax exp), Some Z.zero
 | "@NaN@" -> false, (emax exp), None
 | "-@NaN@" -> true, (emax exp), None
 | _ -> let min_exp = emin_normal e in
 let significand = Z.of_string digits in
 let scaled_significand = if exp < min_exp then 
   (Z.shift_right significand (min_exp - (exp - 1))) else 
   significand in
 let true_exp = if exp < min_exp then min_exp else exp in
 (String.get digits 0 = '-'), true_exp, Some scaled_significand

let float_regexp = Str.regexp "(.*)[pP]([0-9]+)[xX]([0-9]+)"

let unescape_k_string (str: string) =
  let str = String.sub str 1 (String.length str - 2) in
  Scanf.unescaped str

let parse_float (str: string) : int * int * string = 
  if Str.string_match float_regexp str 0 then
    let prec = int_of_string (Str.matched_group 2 str) in
    let exp = int_of_string (Str.matched_group 3 str) in
    (prec, exp, (Str.matched_group 1 str))
  else let last_idx = String.length str - 1 in
  let last = String.get str last_idx in match last with
  | 'f' | 'F' -> (24, 8, String.sub str 0 last_idx)
  | 'd' | 'D' -> (53, 11, String.sub str 0 last_idx)
  | _ -> (53, 11, str)

let ktoken (s: sort) (str: string) : kitem = match s with
| SortInt -> Int (Z.of_string str)
| SortFloat -> let (p,e,f) = parse_float str in (round_to_range(Float ((Gmp.FR.from_string_prec_base p Gmp.GMP_RNDN 10 f), e, p)))
| SortString -> String (unescape_k_string str)
| SortBool -> Bool (bool_of_string str)
| _ -> KToken(s,str)

let get_exit_code(subst: k Subst.t) : int = match (Subst.fold (fun k v res -> match (v, res) with
    [Int i], None -> Some (Z.to_int i)
  | [Int i], Some _ -> failwith "Bad exit code pattern"
  | _ -> res) subst None) with Some i -> i | _ -> failwith "Bad exit code pattern"

module MAP =
struct

  let hook_element c lbl sort config ff = match c with 
      k1, k2 -> [Map (sort,(collection_for lbl),(KMap.singleton k1 k2))]
  let hook_unit c lbl sort config ff = match c with 
      () -> [Map (sort,(collection_for lbl),KMap.empty)]
  let hook_concat c lbl sort config ff = match c with 
      ([Map (s,l1,k1)]), ([Map (_,l2,k2)]) 
        when (l1 = l2) -> [Map (s,l1,(KMap.merge (fun k a b -> match a, b with 
                          None, None -> None 
                        | None, Some v 
                        | Some v, None -> Some v 
                        | Some v1, Some v2 when v1 = v2 -> Some v1) k1 k2))]
    | _ -> raise Not_implemented
  let hook_lookup c lbl sort config ff = match c with 
      [Map (_,_,k1)], k2 -> (try KMap.find k2 k1 with Not_found -> [Bottom])
    | _ -> raise Not_implemented
  let hook_update c lbl sort config ff = match c with 
      [Map (s,l,k1)], k, v -> [Map (s,l,(KMap.add k v k1))]
    | _ -> raise Not_implemented
  let hook_remove c lbl sort config ff = match c with 
      [Map (s,l,k1)], k2 -> [Map (s,l,(KMap.remove k2 k1))]
    | _ -> raise Not_implemented
  let hook_difference c lbl sort config ff = match c with
      [Map (s,l1,k1)], [Map (_,l2,k2)]
        when (l1 = l2) -> [Map (s,l1,(KMap.filter (fun k v -> try (compare (KMap.find k k2) v) <> 0 with Not_found -> true) k1))]
    | _ -> raise Not_implemented
  let hook_keys c lbl sort config ff = match c with 
      [Map (_,_,k1)] -> [Set (SortSet, Lbl_Set_,(KMap.fold (fun k v -> KSet.add k) k1 KSet.empty))]
    | _ -> raise Not_implemented
  let hook_in_keys c lbl sort config ff = match c with
      (k1, [Map (_,_,k2)]) -> [Bool (KMap.mem k1 k2)]
    | _ -> raise Not_implemented
  let hook_values c lbl sort config ff = match c with 
      [Map (_,_,k1)] -> [List (SortList, Lbl_List_,(match List.split (KMap.bindings k1) with (_,vs) -> vs))]
    | _ -> raise Not_implemented
  let hook_choice c lbl sort config ff = match c with 
      [Map (_,_,k1)] -> (match KMap.choose k1 with (k, _) -> k)
    | _ -> raise Not_implemented
  let hook_size c lbl sort config ff = match c with 
      [Map (_,_,m)] -> [Int (Z.of_int (KMap.cardinal m))]
    | _ -> raise Not_implemented
  let hook_inclusion c lbl sort config ff = match c with
      [Map (s,l1,k1)], [Map (_,l2,k2)] 
        when (l1 = l2) -> [Bool (KMap.for_all (fun k v -> try (compare (KMap.find k k2) v) = 0 with Not_found -> false) k1)]
    | _ -> raise Not_implemented
  let hook_updateAll c lbl sort config ff = match c with 
      ([Map (s,l1,k1)]), ([Map (_,l2,k2)]) 
        when (l1 = l2) -> [Map (s,l1,(KMap.merge (fun k a b -> match a, b with 
                          None, None -> None 
                        | None, Some v 
                        | Some v, None 
                        | Some _, Some v -> Some v) k1 k2))]
    | _ -> raise Not_implemented
  let hook_removeAll c lbl sort config ff = match c with
      [Map (s,l,k1)], [Set (_,_,k2)] -> [Map (s,l,KMap.filter (fun k v -> not (KSet.mem k k2)) k1)]
    | _ -> raise Not_implemented
end

module SET =
struct
  let hook_in c lbl sort config ff = match c with
      k1, [Set (_,_,k2)] -> [Bool (KSet.mem k1 k2)]
    | _ -> raise Not_implemented
  let hook_unit c lbl sort config ff = match c with
      () -> [Set (sort,(collection_for lbl),KSet.empty)]
  let hook_element c lbl sort config ff = match c with
      k -> [Set (sort,(collection_for lbl),(KSet.singleton k))]
  let hook_concat c lbl sort config ff = match c with
      [Set (sort,l1,s1)], [Set (_,l2,s2)] when (l1 = l2) -> [Set (sort,l1,(KSet.union s1 s2))]
    | _ -> raise Not_implemented
  let hook_difference c lbl sort config ff = match c with
      [Set (s,l1,k1)], [Set (_,l2,k2)] when (l1 = l2) -> [Set (s,l1,(KSet.diff k1 k2))]
    | _ -> raise Not_implemented
  let hook_inclusion c lbl sort config ff = match c with
      [Set (s,l1,k1)], [Set (_,l2,k2)] when (l1 = l2) -> [Bool (KSet.subset k1 k2)]
    | _ -> raise Not_implemented
  let hook_intersection c lbl sort config ff = match c with
      [Set (s,l1,k1)], [Set (_,l2,k2)] when (l1 = l2) -> [Set (s,l1,(KSet.inter k1 k2))]
    | _ -> raise Not_implemented
  let hook_choice c lbl sort config ff = match c with
      [Set (_,_,k1)] -> KSet.choose k1
    | _ -> raise Not_implemented
  let hook_size c lbl sort config ff = match c with
      [Set (_,_,s)] -> [Int (Z.of_int (KSet.cardinal s))]
    | _ -> raise Not_implemented
end

module LIST =
struct
  let hook_unit c lbl sort config ff = match c with
      () -> [List (sort,(collection_for lbl),[])]
  let hook_element c lbl sort config ff = match c with
      k -> [List (sort,(collection_for lbl),[k])]
  let hook_concat c lbl sort config ff = match c with
      [List (s,lbl1,l1)], [List (_,lbl2,l2)] when (lbl1 = lbl2) -> [List (s,lbl1,(l1 @ l2))]
    | _ -> raise Not_implemented
  let hook_in c lbl sort config ff = match c with
      k1, [List (_,_,k2)] -> [Bool (List.mem k1 k2)]
    | _ -> raise Not_implemented
  let hook_get c lbl sort config ff = match c with
      [List (_,_,l1)], [Int i] -> 
        let i = Z.to_int i in (try if i >= 0 then List.nth l1 i else List.nth l1 ((List.length l1) + i) 
                               with Failure "nth" -> [Bottom] | Invalid_argument "List.nth" -> [Bottom])
    | _ -> raise Not_implemented
  let hook_range c lbl sort config ff = match c with
      [List (s,lbl,l1)], [Int i1], [Int i2] -> 
        (try [List (s,lbl,(list_range (l1, (Z.to_int i1), (List.length(l1) - (Z.to_int i2) - (Z.to_int i1)))))] 
         with Failure "list_range" -> [Bottom])
    | _ -> raise Not_implemented
  let hook_size c lbl sort config ff = match c with
      [List (_,_,l)] -> [Int (Z.of_int (List.length l))]
    | _ -> raise Not_implemented
end

module KREFLECTION = 
struct
  let hook_sort c lbl sort config ff = match c with
      
      [KToken (sort, s)] -> [String (print_sort(sort))]
    | [Int _] -> [String "Int"]
    | [String _] -> [String "String"]
    | [Bool _] -> [String "Bool"]
    | [Map (s,_,_)] -> [String (print_sort s)]
    | [List (s,_,_)] -> [String (print_sort s)]
    | [Set (s,_,_)] -> [String (print_sort s)]
    | _ -> raise Not_implemented
  let hook_getKLabel c lbl sort config ff = match c with
      [k] -> (match (normalize k) with KApply (lbl, _) -> [InjectedKLabel lbl] | _ -> [Bottom])
    | _ -> [Bottom]
  let hook_configuration c lbl sort config ff = match c with
      () -> config
  let hook_fresh c lbl sort config ff = match c with
      [String sort] -> let res = ff sort config !freshCounter in freshCounter := Z.add !freshCounter Z.one; res
    | _ -> raise Not_implemented
  let hook_argv c lbl sort config ff = match c with
      () -> [List (SortList, Lbl_List_,(Array.fold_right (fun arg res -> [String arg] :: res) Sys.argv []))]
end

module KEQUAL =
struct
  let hook_eq c lbl sort config ff = match c with
      k1, k2 -> [Bool ((compare k1 k2) = 0)]
  let hook_ne c lbl sort config ff = match c with
      k1, k2 -> [Bool ((compare k1 k2) <> 0)]
  let hook_ite c lbl sort config ff = match c with
      [Bool t], k1, k2 -> if t then k1 else k2
    | _ -> raise Not_implemented
end

module IO =
struct
  let hook_close c lbl sort config ff = match c with
      [Int i] -> Unix.close (Hashtbl.find file_descriptors i); []
    | _ -> raise Not_implemented
  let hook_getc c lbl sort config ff = match c with
      [Int i] -> let b = Bytes.create 1 in let _ = Unix.read (Hashtbl.find file_descriptors i) b 0 1 in [Int (Z.of_int (Char.code (Bytes.get b 0)))]
    | _ -> raise Not_implemented
  let hook_open c lbl sort config ff = match c with
      [String path], [String flags] -> 
        let fd = Unix.openfile path (convert_open_flags flags) default_file_perm in
          let fd_int = !curr_fd in Hashtbl.add file_descriptors fd_int fd; curr_fd := (Z.add fd_int Z.one); [Int fd_int]
    | _ -> raise Not_implemented
  let hook_putc c lbl sort config ff = match c with
      [Int fd], [Int c] -> let _ = Unix.write (Hashtbl.find file_descriptors fd) (Bytes.make 1 (Char.chr (Z.to_int c))) 0 1 in []
    | _ -> raise Not_implemented
  let hook_read c lbl sort config ff = match c with
      [Int fd], [Int len] -> let l = (Z.to_int len) in 
        let b = Bytes.create l in let _ = Unix.read (Hashtbl.find file_descriptors fd) b 0 l in [String (Bytes.to_string b)]
    | _ -> raise Not_implemented
  let hook_seek c lbl sort config ff = match c with
      [Int fd], [Int off] -> let o = (Z.to_int off) in let _ = Unix.lseek (Hashtbl.find file_descriptors fd) o Unix.SEEK_SET in []
    | _ -> raise Not_implemented
  let hook_tell c lbl sort config ff = match c with
      [Int fd] -> [Int (Z.of_int (Unix.lseek (Hashtbl.find file_descriptors fd) 0 Unix.SEEK_CUR))]
    | _ -> raise Not_implemented
  let hook_write c lbl sort config ff = match c with
      [Int fd], [String s] -> let b = Bytes.of_string s in let _ = Unix.write (Hashtbl.find file_descriptors fd) b 0 (Bytes.length b) in []
    | _ -> raise Not_implemented

  let hook_stat c lbl sort config ff = raise Not_implemented
  let hook_lstat c lbl sort config ff = raise Not_implemented
  let hook_opendir c lbl sort config ff = raise Not_implemented
  let hook_parse c lbl sort config ff = raise Not_implemented
  let hook_parseInModule c lbl sort config ff = raise Not_implemented
  let hook_system c lbl sort config ff = raise Not_implemented
end

module BOOL = 
struct
  let hook_and c lbl sort config ff = match c with
      [Bool b1], [Bool b2] -> [Bool (b1 && b2)]
    | _ -> raise Not_implemented
  let hook_andThen = hook_and
  let hook_or c lbl sort config ff = match c with
      [Bool b1], [Bool b2] -> [Bool (b1 || b2)]
    | _ -> raise Not_implemented
  let hook_orElse = hook_or
  let hook_not c lbl sort config ff = match c with
      [Bool b1] -> [Bool (not b1)]
    | _ -> raise Not_implemented
  let hook_implies c lbl sort config ff = match c with
      [Bool b1], [Bool b2] -> [Bool ((not b1) || b2)]
    | _ -> raise Not_implemented
  let hook_ne c lbl sort config ff = match c with
      [Bool b1], [Bool b2] -> [Bool (b1 <> b2)]
    | _ -> raise Not_implemented
  let hook_eq c lbl sort config ff = match c with
      [Bool b1], [Bool b2] -> [Bool (b1 = b2)]
    | _ -> raise Not_implemented
  let hook_xor = hook_ne
end

module STRING =
struct
  let hook_concat c lbl sort config ff = match c with
      [String s1], [String s2] -> [String (s1 ^ s2)]
    | _ -> raise Not_implemented
  let hook_lt c lbl sort config ff = match c with
      [String s1], [String s2] -> [Bool ((String.compare s1 s2) < 0)]
    | _ -> raise Not_implemented
  let hook_le c lbl sort config ff = match c with
      [String s1], [String s2] -> [Bool ((String.compare s1 s2) <= 0)]
    | _ -> raise Not_implemented
  let hook_gt c lbl sort config ff = match c with
      [String s1], [String s2] -> [Bool ((String.compare s1 s2) > 0)]
    | _ -> raise Not_implemented
  let hook_ge c lbl sort config ff = match c with
      [String s1], [String s2] -> [Bool ((String.compare s1 s2) >= 0)]
    | _ -> raise Not_implemented
  let hook_eq c lbl sort config ff = match c with
      [String s1], [String s2] -> [Bool (s1 = s2)]
    | _ -> raise Not_implemented
  let hook_ne c lbl sort config ff = match c with
      [String s1], [String s2] -> [Bool (s1 <> s2)]
    | _ -> raise Not_implemented
  let hook_chr c lbl sort config ff = match c with
      [Int i] -> [String (String.make 1 (Char.chr (Z.to_int i)))]
    | _ -> raise Not_implemented
  let hook_find c lbl sort config ff = match c with
      [String s1], [String s2], [Int i] -> 
        (try [Int (Z.of_int (Str.search_forward (Str.regexp_string s2) s1 (Z.to_int i)))] 
        with Not_found -> [Int (Z.of_int (-1))])
    | _ -> raise Not_implemented
  let hook_rfind c lbl sort config ff = match c with
      [String s1], [String s2], [Int i] -> 
        (try [Int (Z.of_int (Str.search_backward (Str.regexp_string s2) s1 (Z.to_int i)))] 
        with Not_found -> [Int (Z.of_int (-1))])
    | _ -> raise Not_implemented
  let hook_length c lbl sort config ff = match c with
      [String s] -> [Int (Z.of_int (String.length s))]
    | _ -> raise Not_implemented
  let hook_substr c lbl sort config ff = match c with
      [String s], [Int i1], [Int i2] -> [String (String.sub s (Z.to_int i1) (Z.to_int (Z.sub i2 i1)))]
    | _ -> raise Not_implemented
  let hook_ord c lbl sort config ff = match c with
      [String s] -> [Int (Z.of_int (Char.code (String.get s 0)))]
    | _ -> raise Not_implemented
  let hook_int2string c lbl sort config ff = match c with
      [Int i] -> [String (Z.to_string i)]
    | _ -> raise Not_implemented
  let hook_string2int c lbl sort config ff = match c with
      [String s] -> [Int (Z.of_string s)]
    | _ -> raise Not_implemented
  let hook_string2base c lbl sort config ff = match c with
      [String s], [Int i] -> [Int (Z.of_string_base (Z.to_int i) s)]
    | _ -> raise Not_implemented
  let hook_base2string c lbl sort config ff = match c with
      [Int i], [Int base] -> [String (to_string_base (Z.to_int base) i)]
    | _ -> raise Not_implemented
  let hook_floatFormat c lbl sort config ff = raise Not_implemented
  let hook_float2string c lbl sort config ff = raise Not_implemented
  let hook_string2float c lbl sort config ff = raise Not_implemented
  let hook_replace c lbl sort config ff = raise Not_implemented
  let hook_replaceAll c lbl sort config ff = raise Not_implemented
  let hook_replaceFirst c lbl sort config ff = raise Not_implemented
  let hook_countAllOccurrences c lbl sort config ff = raise Not_implemented
  let hook_category c lbl sort config ff = raise Not_implemented
  let hook_directionality c lbl sort config ff = raise Not_implemented
  let hook_findChar c lbl sort config ff = raise Not_implemented
  let hook_rfindChar c lbl sort config ff = raise Not_implemented
end

open Gmp.RNG

module INT =
struct
  let hook_tmod c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.rem a b)]
    | _ -> raise Not_implemented
  let hook_add c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.add a b)]
    | _ -> raise Not_implemented
  let hook_le c lbl sort config ff = match c with
      [Int a], [Int b] -> [Bool (Z.leq a b)]
    | _ -> raise Not_implemented
  let hook_eq c lbl sort config ff = match c with
      [Int a], [Int b] -> [Bool (Z.equal a b)]
    | _ -> raise Not_implemented
  let hook_ne c lbl sort config ff = match c with
      [Int a], [Int b] -> [Bool (not (Z.equal a b))]
    | _ -> raise Not_implemented
  let hook_and c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.logand a b)]
    | _ -> raise Not_implemented
  let hook_mul c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.mul a b)]
    | _ -> raise Not_implemented
  let hook_sub c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.sub a b)]
    | _ -> raise Not_implemented
  let hook_tdiv c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.div a b)]
    | _ -> raise Not_implemented
  let hook_shl c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.shift_left a (Z.to_int b))]
    | _ -> raise Not_implemented
  let hook_lt c lbl sort config ff = match c with
      [Int a], [Int b] -> [Bool (Z.lt a b)]
    | _ -> raise Not_implemented
  let hook_ge c lbl sort config ff = match c with
      [Int a], [Int b] -> [Bool (Z.geq a b)]
    | _ -> raise Not_implemented
  let hook_shr c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.shift_right a (Z.to_int b))]
    | _ -> raise Not_implemented
  let hook_gt c lbl sort config ff = match c with
      [Int a], [Int b] -> [Bool (Z.gt a b)]
    | _ -> raise Not_implemented
  let hook_pow c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.pow a (Z.to_int b))]
    | _ -> raise Not_implemented
  let hook_xor c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.logxor a b)]
    | _ -> raise Not_implemented
  let hook_or c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.logor a b)]
    | _ -> raise Not_implemented
  let hook_not c lbl sort config ff = match c with
      [Int a] -> [Int (Z.lognot a)]
    | _ -> raise Not_implemented
  let hook_abs c lbl sort config ff = match c with
      [Int a] -> [Int (Z.abs a)]
    | _ -> raise Not_implemented
  let hook_max c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.max a b)]
    | _ -> raise Not_implemented
  let hook_min c lbl sort config ff = match c with
      [Int a], [Int b] -> [Int (Z.min a b)]
    | _ -> raise Not_implemented
  let hook_rand c lbl sort config ff = match c with
      [Int max] -> let mpz = Gmp.Z.urandomm Gmp.RNG.default (from_zarith max) in
          [Int (to_zarith mpz)]
    | _ -> raise Not_implemented
  let hook_srand c lbl sort config ff = match c with
      [Int seed] -> let () = Gmp.Z.randseed Gmp.RNG.default (from_zarith seed) in []
    | _ -> raise Not_implemented
  let hook_ediv c lbl sort config ff = raise Not_implemented
  let hook_emod c lbl sort config ff = raise Not_implemented
end

module FLOAT =
struct
  let hook_isNaN c lbl sort config ff = match c with
      [Float (f,_,_)] -> [Bool (Gmp.FR.is_nan f)]
    | _ -> raise Not_implemented
  let hook_maxValue c lbl sort config ff = match c with
      [Int prec], [Int exp] -> let e = Z.to_int exp and p = Z.to_int prec in
        [round_to_range(Float ((Gmp.FR.nexttoward (emin e p) (emax e) (Gmp.FR.from_string_prec_base p Gmp.GMP_RNDN 10 "inf") Gmp.FR.zero),e,p))]
    | _ -> raise Not_implemented
  let hook_minValue c lbl sort config ff = match c with
      [Int prec], [Int exp] -> let e = Z.to_int exp and p = Z.to_int prec in
        [round_to_range(Float ((Gmp.FR.nexttoward (emin e p) (emax e) Gmp.FR.zero (Gmp.FR.from_string_prec_base p Gmp.GMP_RNDN 10 "inf")),e,p))]
    | _ -> raise Not_implemented
  let hook_round c lbl sort config ff = match c with
      [Float (f,_,_)], [Int prec], [Int exp] ->
        [round_to_range (Float (f,(Z.to_int exp),(Z.to_int prec)))]
    | _ -> raise Not_implemented
  let hook_abs c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.abs_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_ceil c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.rint_prec p Gmp.GMP_RNDU f),e,p))]
    | _ -> raise Not_implemented
  let hook_floor c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.rint_prec p Gmp.GMP_RNDD f),e,p))]
    | _ -> raise Not_implemented
  let hook_acos c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.acos_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_asin c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.asin_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_atan c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.atan_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_cos c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.cos_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_sin c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.sin_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_tan c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.tan_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_exp c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.exp_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_log c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.log_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_neg c lbl sort config ff = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.neg_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_add c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] 
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.add_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_sub c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] 
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.sub_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_mul c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] 
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.mul_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_div c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] 
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.div_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_pow c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)]
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.pow_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_eq c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] -> [Bool (Gmp.FR.equal f1 f2)]
    | _ -> raise Not_implemented
  let hook_lt c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] -> [Bool (Gmp.FR.less f1 f2)]
    | _ -> raise Not_implemented
  let hook_le c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] -> [Bool (Gmp.FR.lessequal f1 f2)]
    | _ -> raise Not_implemented
  let hook_gt c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] -> [Bool (Gmp.FR.greater f1 f2)]
    | _ -> raise Not_implemented
  let hook_ge c lbl sort config ff = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)] -> [Bool (Gmp.FR.greaterequal f1 f2)]
    | _ -> raise Not_implemented
  let hook_precision c lbl sort config ff = match c with
      [Float (_,_,p)] -> [Int (Z.of_int p)]
    | _ -> raise Not_implemented
  let hook_exponentBits c lbl sort config ff = match c with
      [Float (_,e,_)] -> [Int (Z.of_int e)]
    | _ -> raise Not_implemented
  let hook_float2int c lbl sort config ff = match c with
      [Float (f,_,_)] -> [Int (to_zarith (Gmp.FR.to_z_f f))]
    | _ -> raise Not_implemented
  let hook_int2float c lbl sort config ff = match c with
      [Int i], [Int prec], [Int exp] -> 
        [round_to_range(Float ((Gmp.FR.from_z_prec (Z.to_int prec) Gmp.GMP_RNDN (from_zarith i)),(Z.to_int exp),(Z.to_int prec)))]
    | _ -> raise Not_implemented
  let hook_min c lbl sort config ff = raise Not_implemented
  let hook_max c lbl sort config ff = raise Not_implemented
  let hook_rem c lbl sort config ff = raise Not_implemented
  let hook_root c lbl sort config ff = raise Not_implemented
  let hook_sign c lbl sort config ff = match c with
      [Float (f,e,p)] -> (match deconstruct_float f e p with (s,_,_) -> [Bool s])
    | _ -> raise Not_implemented
  let hook_significand c lbl sort config ff = match c with
      [Float (f,e,p)] -> (match deconstruct_float f e p with (_, _, Some s) -> [Int s] 
        | _ -> raise Not_implemented)
    | _ -> raise Not_implemented
  let hook_atan2 c lbl sort config ff = raise Not_implemented
  let hook_exponent c lbl sort config ff = match c with
      [Float (f,e,p)] -> (match deconstruct_float f e p with (_, exp, _) -> [Int (Z.of_int exp)])
    | _ -> raise Not_implemented
end
