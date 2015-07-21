open Gmp
open Constants
module type S =
sig
  type 'a m
  type s
  type t = kitem list
 and kitem = KApply of klabel * t list
           | KToken of sort * string
           | InjectedKLabel of klabel
           | Map of sort * klabel * t m
           | List of sort * klabel * t list
           | Set of sort * klabel * s
           | Int of Z.t
           | Float of FR.t * int * int
           | String of string
           | Bool of bool
           | Bottom
  val compare : t -> t -> int
  val compare_kitem : kitem -> kitem -> int
end 


module rec K : (S with type 'a m = 'a Map.Make(K).t and type s = Set.Make(K).t)  = 
struct
  module KMap = Map.Make(K)
  module KSet = Set.Make(K)
  type 'a m = 'a KMap.t
  and s = KSet.t
  and t = kitem list
 and kitem = KApply of klabel * t list
           | KToken of sort * string
           | InjectedKLabel of klabel
           | Map of sort * klabel * t m
           | List of sort * klabel * t list
           | Set of sort * klabel * s
           | Int of Z.t
           | Float of FR.t * int * int
           | String of string
           | Bool of bool
           | Bottom
  let rec compare c1 c2 = if c1 == c2 then 0 else match (c1, c2) with
    | [], [] -> 0
    | (hd1 :: tl1), (hd2 :: tl2) -> let v = compare_kitem hd1 hd2 in if v = 0 then compare tl1 tl2 else v
    | (hd1 :: tl1), _ -> -1
    | _ -> 1
  and compare_kitem c1 c2 = match (c1, c2) with
    | (KApply(kl1, k1)), (KApply(kl2, k2)) -> let v = Pervasives.compare kl1 kl2 in if v = 0 then compare_klist k1 k2 else v
    | (KToken(s1, st1)), (KToken(s2, st2)) -> let v = Pervasives.compare s1 s2 in if v = 0 then Pervasives.compare st1 st2 else v
    | (InjectedKLabel kl1), (InjectedKLabel kl2) -> Pervasives.compare kl1 kl2
    | (Map (_,k1,m1)), (Map (_,k2,m2)) -> let v = Pervasives.compare k1 k2 in if v = 0 then (KMap.compare) compare m1 m2 else v
    | (List (_,k1,l1)), (List (_,k2,l2)) -> let v = Pervasives.compare k1 k2 in if v = 0 then compare_klist l1 l2 else v
    | (Set (_,k1,s1)), (Set (_,k2,s2)) -> let v = Pervasives.compare k1 k2 in if v = 0 then (KSet.compare) s1 s2 else v
    | (Int i1), (Int i2) -> Z.compare i1 i2
    | (Float (f1,e1,p1)), (Float (f2,e2,p2)) -> let v = e2 - e1 in if v = 0 then let v2 = p2 - p1 in if v2 = 0 then FR.compare f1 f2 else v2 else v
    | (String s1), (String s2) -> Pervasives.compare s1 s2
    | (Bool b1), (Bool b2) -> if b1 = b2 then 0 else if b1 then -1 else 1
    | Bottom, Bottom -> 0
    | KApply(_, _), _ -> -1
    | _, KApply(_, _) -> 1
    | KToken(_, _), _ -> -1
    | _, KToken(_, _) -> 1
    | InjectedKLabel(_), _ -> -1
    | _, InjectedKLabel(_) -> 1
    | Map(_), _ -> -1
    | _, Map(_) -> 1
    | List(_), _ -> -1
    | _, List(_) -> 1
    | Set(_), _ -> -1
    | _, Set(_) -> 1
    | Int(_), _ -> -1
    | _, Int(_) -> 1
    | Float(_), _ -> -1
    | _, Float(_) -> 1
    | String(_), _ -> -1
    | _, String(_) -> 1
    | Bool(_), _ -> -1
    | _, Bool(_) -> 1
  and compare_klist c1 c2 = match (c1, c2) with
    | [], [] -> 0
    | (hd1 :: tl1), (hd2 :: tl2) -> let v = compare hd1 hd2 in if v = 0 then compare_klist tl1 tl2 else v
    | (hd1 :: tl1), _ -> -1
    | _ -> 1
end

module KMap = Map.Make(K)
module KSet = Set.Make(K)

open K
type k = K.t
exception Stuck of k
exception Not_implemented
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
let float_to_string (f: FR.t) : string = if FR.is_nan f then "NaN" else if FR.is_inf f then if FR.sgn f > 0 then "Infinity" else "-Infinity" else FR.to_string_base_digits GMP_RNDN 10 0 f
let k_of_list lbl l = match l with 
  [] -> KApply((unit_for lbl),[])
| hd :: tl -> List.fold_left (fun list el -> KApply(lbl, [list] :: [KApply((el_for lbl),[el])] :: [])) (KApply((el_for lbl),[hd])) tl
let k_of_set lbl s = if (KSet.cardinal s) = 0 then KApply((unit_for lbl),[]) else 
  let hd = KSet.choose s in KSet.fold (fun el set -> KApply(lbl, [set] :: [KApply((el_for lbl),[el])] :: [])) (KSet.remove hd s) (KApply((el_for lbl),[hd]))
let k_of_map lbl m = if (KMap.cardinal m) = 0 then KApply((unit_for lbl),[]) else 
  let (k,v) = KMap.choose m in KMap.fold (fun k v map -> KApply(lbl, [map] :: [KApply((el_for lbl),[k;v])] :: [])) (KMap.remove k m) (KApply((el_for lbl),[k;v]))
let rec print_klist(c: k list) : string = match c with
| [] -> ".KList"
| e::[] -> print_k(e)
| e1::e2::l -> print_k(e1) ^ ", " ^ print_klist(e2::l)
and print_k(c: k) : string = match c with
| [] -> ".K"
| e::[] -> print_kitem(e)
| e1::e2::l -> print_kitem(e1) ^ " ~> " ^ print_k(e2::l)
and print_kitem(c: kitem) : string = match c with
| KApply(klabel, klist) -> print_klabel(klabel) ^ "(" ^ print_klist(klist) ^ ")"
| KToken(sort, s) -> "#token(\"" ^ (String.escaped s) ^ "\", \"" ^ print_sort(sort) ^ "\")"
| InjectedKLabel(klabel) -> "#klabel(" ^ print_klabel(klabel) ^ ")"
| Bool(b) -> print_kitem(KToken(Constants.boolSort, string_of_bool(b)))
| String(s) -> print_kitem(KToken(Constants.stringSort, "\"" ^ (String.escaped s) ^ "\""))
| Int(i) -> print_kitem(KToken(Constants.intSort, Z.to_string(i)))
| Float(f,_,_) -> print_kitem(KToken(Constants.floatSort, float_to_string(f)))
| Bottom -> "`#Bottom`(.KList)"
| List(_,lbl,l) -> print_kitem(k_of_list lbl l)
| Set(_,lbl,s) -> print_kitem(k_of_set lbl s)
| Map(_,lbl,m) -> print_kitem(k_of_map lbl m)
module Subst = Map.Make(String)
let print_subst (out: out_channel) (c: k Subst.t) : unit = 
  output_string out "1\n"; Subst.iter (fun v k -> output_string out (v ^ "\n" ^ (print_k k) ^ "\n")) c
let emin (exp: int) (prec: int) : int = (- (1 lsl (exp - 1))) + 4 - prec
let emax (exp: int) : int = 1 lsl (exp - 1)
let round_to_range (c: kitem) : kitem = match c with 
    Float(f,e,p) -> let (cr, t) = (FR.check_range p GMP_RNDN (emin e p) (emax e) f) in Float((FR.subnormalize cr t GMP_RNDN),e,p)
  | _ -> raise (Invalid_argument "round_to_range")
let curr_fd : Z.t ref = ref (Z.of_int 3)
let file_descriptors = let m = Hashtbl.create 5 in Hashtbl.add m (Z.from_int 0) Unix.stdin; Hashtbl.add m (Z.from_int 1) Unix.stdout; Hashtbl.add m (Z.from_int 2) Unix.stderr; m
let default_file_perm = let v = Unix.umask 0 in let _ = Unix.umask v in (lnot v) land 0o777
let convert_open_flags (s: string) : Unix.open_flag list = 
  match s with 
      "r" -> [Unix.O_RDONLY] 
    | "w" -> [Unix.O_WRONLY] 
    | "rw" -> [Unix.O_RDWR]
    | _ -> raise (Invalid_argument "convert_open_flags")

module MAP =
struct

  let hook_element c lbl sort config ff = match c with 
      k1 :: k2 :: [] -> [Map (sort,(collection_for lbl),(KMap.singleton k1 k2))]
    | _ -> raise Not_implemented
  let hook_unit c lbl sort config ff = match c with 
      [] -> [Map (sort,(collection_for lbl),KMap.empty)]
    | _ -> raise Not_implemented
  let hook_concat c lbl sort config ff = match c with 
      ([Map (s,l1,k1)]) :: ([Map (_,l2,k2)]) :: [] 
        when (l1 = l2) -> [Map (s,l1,(KMap.merge (fun k a b -> match a, b with 
                          None, None -> None 
                        | None, Some v 
                        | Some v, None -> Some v 
                        | Some v1, Some v2 when v1 = v2 -> Some v1) k1 k2))]
    | _ -> raise Not_implemented
  let hook_lookup c lbl sort config ff = match c with 
      [Map (_,_,k1)] :: k2 :: [] -> (try KMap.find k2 k1 with Not_found -> [Bottom])
    | _ -> raise Not_implemented
  let hook_update c lbl sort config ff = match c with 
      [Map (s,l,k1)] :: k :: v :: [] -> [Map (s,l,(KMap.add k v k1))]
    | _ -> raise Not_implemented
  let hook_remove c lbl sort config ff = match c with 
      [Map (s,l,k1)] :: k2 :: [] -> [Map (s,l,(KMap.remove k2 k1))]
    | _ -> raise Not_implemented
  let hook_difference c lbl sort config ff = match c with
      [Map (s,l1,k1)] :: [Map (_,l2,k2)] :: []
        when (l1 = l2) -> [Map (s,l1,(KMap.filter (fun k v -> try (compare (KMap.find k k2) v) <> 0 with Not_found -> true) k1))]
    | _ -> raise Not_implemented
  let hook_keys c lbl sort config ff = match c with 
      [Map (_,_,k1)] :: [] -> [Set (Constants.setSort, Constants.setConcatLabel,(KMap.fold (fun k v -> KSet.add k) k1 KSet.empty))]
    | _ -> raise Not_implemented
  let hook_values c lbl sort config ff = match c with 
      [Map (_,_,k1)] :: [] -> [List (Constants.listSort, Constants.listConcatLabel,(match List.split (KMap.bindings k1) with (_,vs) -> vs))]
    | _ -> raise Not_implemented
  let hook_choice c lbl sort config ff = match c with 
      [Map (_,_,k1)] :: [] -> (match KMap.choose k1 with (k, _) -> k)
    | _ -> raise Not_implemented
  let hook_size c lbl sort config ff = match c with 
      [Map (_,_,m)] :: [] -> [Int (Z.of_int (KMap.cardinal m))]
    | _ -> raise Not_implemented
  let hook_inclusion c lbl sort config ff = match c with
      [Map (s,l1,k1)] :: [Map (_,l2,k2)] :: [] 
        when (l1 = l2) -> [Bool (KMap.for_all (fun k v -> try (compare (KMap.find k k2) v) = 0 with Not_found -> false) k1)]
    | _ -> raise Not_implemented
  let hook_updateAll c lbl sort config ff = match c with 
      ([Map (s,l1,k1)]) :: ([Map (_,l2,k2)]) :: [] 
        when (l1 = l2) -> [Map (s,l1,(KMap.merge (fun k a b -> match a, b with 
                          None, None -> None 
                        | None, Some v 
                        | Some v, None 
                        | Some _, Some v -> Some v) k1 k2))]
    | _ -> raise Not_implemented
  let hook_removeAll c lbl sort config ff = match c with
      [Map (s,l,k1)] :: [Set (_,_,k2)] :: [] -> [Map (s,l,KMap.filter (fun k v -> not (KSet.mem k k2)) k1)]
    | _ -> raise Not_implemented
end

module SET =
struct
  let hook_in c lbl sort config ff = match c with
      k1 :: [Set (_,_,k2)] :: [] -> [Bool (KSet.mem k1 k2)]
    | _ -> raise Not_implemented
  let hook_unit c lbl sort config ff = match c with
      [] -> [Set (sort,(collection_for lbl),KSet.empty)]
    | _ -> raise Not_implemented
  let hook_element c lbl sort config ff = match c with
      k :: [] -> [Set (sort,(collection_for lbl),(KSet.singleton k))]
    | _ -> raise Not_implemented
  let hook_concat c lbl sort config ff = match c with
      [Set (sort,l1,s1)] :: [Set (_,l2,s2)] :: [] when (l1 = l2) -> [Set (sort,l1,(KSet.union s1 s2))]
    | _ -> raise Not_implemented
  let hook_difference c lbl sort config ff = match c with
      [Set (s,l1,k1)] :: [Set (_,l2,k2)] :: [] when (l1 = l2) -> [Set (s,l1,(KSet.diff k1 k2))]
    | _ -> raise Not_implemented
  let hook_inclusion c lbl sort config ff = match c with
      [Set (s,l1,k1)] :: [Set (_,l2,k2)] :: [] when (l1 = l2) -> [Bool (KSet.subset k1 k2)]
    | _ -> raise Not_implemented
  let hook_intersection c lbl sort config ff = match c with
      [Set (s,l1,k1)] :: [Set (_,l2,k2)] :: [] when (l1 = l2) -> [Set (s,l1,(KSet.inter k1 k2))]
    | _ -> raise Not_implemented
  let hook_choice c lbl sort config ff = match c with
      [Set (_,_,k1)] :: [] -> KSet.choose k1
    | _ -> raise Not_implemented
  let hook_size c lbl sort config ff = match c with
      [Set (_,_,s)] :: [] -> [Int (Z.of_int (KSet.cardinal s))]
    | _ -> raise Not_implemented
end

module LIST =
struct
  let hook_unit c lbl sort config ff = match c with
      [] -> [List (sort,(collection_for lbl),[])]
    | _ -> raise Not_implemented
  let hook_element c lbl sort config ff = match c with
      k :: [] -> [List (sort,(collection_for lbl),[k])]
    | _ -> raise Not_implemented
  let hook_concat c lbl sort config ff = match c with
      [List (s,lbl1,l1)] :: [List (_,lbl2,l2)] :: [] when (lbl1 = lbl2) -> [List (s,lbl1,(l1 @ l2))]
    | _ -> raise Not_implemented
  let hook_in c lbl sort config ff = match c with
      k1 :: [List (_,_,k2)] :: [] -> [Bool (List.mem k1 k2)]
    | _ -> raise Not_implemented
  let hook_get c lbl sort config ff = match c with
      [List (_,_,l1)] :: [Int i] :: [] -> 
        let i = Z.to_int i in (try if i >= 0 then List.nth l1 i else List.nth l1 ((List.length l1) + i) 
                               with Failure "nth" -> [Bottom] | Invalid_argument "List.nth" -> [Bottom])
    | _ -> raise Not_implemented
  let hook_range c lbl sort config ff = match c with
      [List (s,lbl,l1)] :: [Int i1] :: [Int i2] :: [] -> 
        (try [List (s,lbl,(list_range (l1, (Z.to_int i1), (List.length(l1) - (Z.to_int i2) - (Z.to_int i1)))))] 
         with Failure "list_range" -> [Bottom])
    | _ -> raise Not_implemented
  let hook_size c lbl sort config ff = match c with
      [List (_,_,l)] :: [] -> [Int (Z.of_int (List.length l))]
    | _ -> raise Not_implemented
end

module KREFLECTION = 
struct
  let hook_sort c lbl sort config ff = match c with
      
      [KToken (sort, s)] :: [] -> [String (print_sort(sort))]
    | [Int _] :: [] -> [String "Int"]
    | [String _] :: [] -> [String "String"]
    | [Bool _] :: [] -> [String "Bool"]
    | [Map (s,_,_)] :: [] -> [String (print_sort s)]
    | [List (s,_,_)] :: [] -> [String (print_sort s)]
    | [Set (s,_,_)] :: [] -> [String (print_sort s)]
    | _ -> raise Not_implemented
  let hook_getKLabel c lbl sort config ff = match c with
      [KApply (lbl, _)] :: [] -> [InjectedKLabel lbl] | _ -> [Bottom]
    | _ -> raise Not_implemented
  let hook_configuration c lbl sort config ff = match c with
      [] -> config
    | _ -> raise Not_implemented
  let hook_fresh c lbl sort config ff = match c with
      [String sort] :: [] -> let res = ff sort config !freshCounter in freshCounter := Z.add !freshCounter Z.one; res
    | _ -> raise Not_implemented
end

module KEQUAL =
struct
  let hook_eq c lbl sort config ff = match c with
      k1 :: k2 :: [] -> [Bool ((compare k1 k2) = 0)]
    | _ -> raise Not_implemented
  let hook_ne c lbl sort config ff = match c with
      k1 :: k2 :: [] -> [Bool ((compare k1 k2) <> 0)]
    | _ -> raise Not_implemented
  let hook_ite c lbl sort config ff = match c with
      [Bool t] :: k1 :: k2 :: [] -> if t then k1 else k2
    | _ -> raise Not_implemented
end

module IO =
struct
  let hook_close c lbl sort config ff = match c with
      [Int i] :: [] -> Unix.close (Hashtbl.find file_descriptors i); []
    | _ -> raise Not_implemented
  let hook_getc c lbl sort config ff = match c with
      [Int i] :: [] -> let b = Bytes.create 1 in let _ = Unix.read (Hashtbl.find file_descriptors i) b 0 1 in [Int (Z.from_int (Char.code (Bytes.get b 0)))]
    | _ -> raise Not_implemented
  let hook_open c lbl sort config ff = match c with
      [String path] :: [String flags] :: [] -> 
        let fd = Unix.openfile path (convert_open_flags flags) default_file_perm in
          let fd_int = !curr_fd in Hashtbl.add file_descriptors fd_int fd; curr_fd := (Z.add fd_int Z.one); [Int fd_int]
    | _ -> raise Not_implemented
  let hook_putc c lbl sort config ff = match c with
      [Int fd] :: [Int c] :: [] -> let _ = Unix.write (Hashtbl.find file_descriptors fd) (Bytes.make 1 (Char.chr (Z.to_int c))) 0 1 in []
    | _ -> raise Not_implemented
  let hook_read c lbl sort config ff = match c with
      [Int fd] :: [Int len] :: [] -> let l = (Z.to_int len) in 
        let b = Bytes.create l in let _ = Unix.read (Hashtbl.find file_descriptors fd) b 0 l in [String (Bytes.to_string b)]
    | _ -> raise Not_implemented
  let hook_seek c lbl sort config ff = match c with
      [Int fd] :: [Int off] :: [] -> let o = (Z.to_int off) in let _ = Unix.lseek (Hashtbl.find file_descriptors fd) o Unix.SEEK_SET in []
    | _ -> raise Not_implemented
  let hook_tell c lbl sort config ff = match c with
      [Int fd] :: [] -> [Int (Z.of_int (Unix.lseek (Hashtbl.find file_descriptors fd) 0 Unix.SEEK_CUR))]
    | _ -> raise Not_implemented
  let hook_write c lbl sort config ff = match c with
      [Int fd] :: [String s] :: [] -> let b = Bytes.of_string s in let _ = Unix.write (Hashtbl.find file_descriptors fd) b 0 (Bytes.length b) in []
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
      [Bool b1] :: [Bool b2] :: [] -> [Bool (b1 && b2)]
    | _ -> raise Not_implemented
  let hook_andThen = hook_and
  let hook_or c lbl sort config ff = match c with
      [Bool b1] :: [Bool b2] :: [] -> [Bool (b1 || b2)]
    | _ -> raise Not_implemented
  let hook_orElse = hook_or
  let hook_not c lbl sort config ff = match c with
      [Bool b1] :: [] -> [Bool (not b1)]
    | _ -> raise Not_implemented
  let hook_implies c lbl sort config ff = match c with
      [Bool b1] :: [Bool b2] :: [] -> [Bool ((not b1) || b2)]
    | _ -> raise Not_implemented
  let hook_ne c lbl sort config ff = match c with
      [Bool b1] :: [Bool b2] :: [] -> [Bool (b1 <> b2)]
    | _ -> raise Not_implemented
  let hook_eq c lbl sort config ff = match c with
      [Bool b1] :: [Bool b2] :: [] -> [Bool (b1 = b2)]
    | _ -> raise Not_implemented
  let hook_xor = hook_ne
end

module STRING =
struct
  let hook_concat c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [] -> [String (s1 ^ s2)]
    | _ -> raise Not_implemented
  let hook_lt c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [] -> [Bool ((String.compare s1 s2) < 0)]
    | _ -> raise Not_implemented
  let hook_le c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [] -> [Bool ((String.compare s1 s2) <= 0)]
    | _ -> raise Not_implemented
  let hook_gt c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [] -> [Bool ((String.compare s1 s2) > 0)]
    | _ -> raise Not_implemented
  let hook_ge c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [] -> [Bool ((String.compare s1 s2) >= 0)]
    | _ -> raise Not_implemented
  let hook_eq c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [] -> [Bool (s1 = s2)]
    | _ -> raise Not_implemented
  let hook_ne c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [] -> [Bool (s1 <> s2)]
    | _ -> raise Not_implemented
  let hook_chr c lbl sort config ff = match c with
      [Int i] :: [] -> [String (String.make 1 (Char.chr (Z.to_int i)))]
    | _ -> raise Not_implemented
  let hook_find c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [Int i] :: [] -> 
        (try [Int (Z.of_int (Str.search_forward (Str.regexp_string s2) s1 (Z.to_int i)))] 
        with Not_found -> [Int (Z.of_int (-1))])
    | _ -> raise Not_implemented
  let hook_rfind c lbl sort config ff = match c with
      [String s1] :: [String s2] :: [Int i] :: [] -> 
        (try [Int (Z.of_int (Str.search_backward (Str.regexp_string s2) s1 (Z.to_int i)))] 
        with Not_found -> [Int (Z.of_int (-1))])
    | _ -> raise Not_implemented
  let hook_length c lbl sort config ff = match c with
      [String s] :: [] -> [Int (Z.of_int (String.length s))]
    | _ -> raise Not_implemented
  let hook_substr c lbl sort config ff = match c with
      [String s] :: [Int i1] :: [Int i2] :: [] -> [String (String.sub s (Z.to_int i1) (Z.to_int (Z.sub i2 i1)))]
    | _ -> raise Not_implemented
  let hook_ord c lbl sort config ff = match c with
      [String s] :: [] -> [Int (Z.of_int (Char.code (String.get s 0)))]
    | _ -> raise Not_implemented
  let hook_int2string c lbl sort config ff = match c with
      [Int i] :: [] -> [String (Z.to_string i)]
    | _ -> raise Not_implemented
  let hook_string2int c lbl sort config ff = match c with
      [String s] :: [] -> [Int (Z.from_string s)]
    | _ -> raise Not_implemented
  let hook_string2base c lbl sort config ff = match c with
      [String s] :: [Int i] :: [] -> [Int (Z.from_string_base (Z.to_int i) s)]
    | _ -> raise Not_implemented
  let hook_base2string c lbl sort config ff = match c with
      [Int i] :: [Int base] :: [] -> [String (Z.to_string_base (Z.to_int base) i)]
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

module INT =
struct
  let hook_tmod c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.tdiv_r a b)]
    | _ -> raise Not_implemented
  let hook_add c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.add a b)]
    | _ -> raise Not_implemented
  let hook_le c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) <= 0)]
    | _ -> raise Not_implemented
  let hook_eq c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) = 0)]
    | _ -> raise Not_implemented
  let hook_ne c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) <> 0)]
    | _ -> raise Not_implemented
  let hook_and c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.band a b)]
    | _ -> raise Not_implemented
  let hook_mul c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.mul a b)]
    | _ -> raise Not_implemented
  let hook_sub c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.sub a b)]
    | _ -> raise Not_implemented
  let hook_tdiv c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.tdiv_q a b)]
    | _ -> raise Not_implemented
  let hook_shl c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.mul_2exp a (Z.to_int b))]
    | _ -> raise Not_implemented
  let hook_lt c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) < 0)]
    | _ -> raise Not_implemented
  let hook_ge c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) >= 0)]
    | _ -> raise Not_implemented
  let hook_shr c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.fdiv_q_2exp a (Z.to_int b))]
    | _ -> raise Not_implemented
  let hook_gt c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) > 0)]
    | _ -> raise Not_implemented
  let hook_pow c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.pow_ui a (Z.to_int b))]
    | _ -> raise Not_implemented
  let hook_xor c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.bxor a b)]
    | _ -> raise Not_implemented
  let hook_or c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.bior a b)]
    | _ -> raise Not_implemented
  let hook_not c lbl sort config ff = match c with
      [Int a] :: [] -> [Int (Z.bcom a)]
    | _ -> raise Not_implemented
  let hook_abs c lbl sort config ff = match c with
      [Int a] :: [] -> [Int (Z.abs a)]
    | _ -> raise Not_implemented
  let hook_max c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.max a b)]
    | _ -> raise Not_implemented
  let hook_min c lbl sort config ff = match c with
      [Int a] :: [Int b] :: [] -> [Int (Z.min a b)]
    | _ -> raise Not_implemented
  let hook_ediv c lbl sort config ff = raise Not_implemented
  let hook_emod c lbl sort config ff = raise Not_implemented
end

module FLOAT =
struct
  let hook_isNaN c lbl sort config ff = match c with
      [Float (f,_,_)] :: [] -> [Bool (FR.is_nan f)]
    | _ -> raise Not_implemented
  let hook_maxValue c lbl sort config ff = match c with
      [Int prec] :: [Int exp] :: [] -> let e = Z.to_int exp and p = Z.to_int prec in
        [round_to_range(Float ((FR.nexttoward (emin e p) (emax e) (FR.from_string_prec_base p GMP_RNDN 10 "inf") FR.zero),e,p))]
    | _ -> raise Not_implemented
  let hook_minValue c lbl sort config ff = match c with
      [Int prec] :: [Int exp] :: [] -> let e = Z.to_int exp and p = Z.to_int prec in
        [round_to_range(Float ((FR.nexttoward (emin e p) (emax e) FR.zero (FR.from_string_prec_base p GMP_RNDN 10 "inf")),e,p))]
    | _ -> raise Not_implemented
  let hook_round c lbl sort config ff = match c with
      [Float (f,_,_)] :: [Int prec] :: [Int exp] :: [] ->
        [round_to_range (Float (f,(Z.to_int exp),(Z.to_int prec)))]
    | _ -> raise Not_implemented
  let hook_abs c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.abs_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_ceil c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.rint_prec p GMP_RNDU f),e,p))]
    | _ -> raise Not_implemented
  let hook_floor c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.rint_prec p GMP_RNDD f),e,p))]
    | _ -> raise Not_implemented
  let hook_acos c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.acos_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_asin c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.asin_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_atan c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.atan_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_cos c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.cos_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_sin c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.sin_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_tan c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.tan_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_exp c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.exp_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_log c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.log_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_neg c lbl sort config ff = match c with
      [Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.neg_prec p GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_add c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] 
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.add_prec p1 GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_sub c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] 
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.sub_prec p1 GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_mul c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] 
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.mul_prec p1 GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_div c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] 
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.div_prec p1 GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_pow c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: []
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.pow_prec p1 GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_eq c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] -> [Bool (FR.equal f1 f2)]
    | _ -> raise Not_implemented
  let hook_lt c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] -> [Bool (FR.less f1 f2)]
    | _ -> raise Not_implemented
  let hook_le c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] -> [Bool (FR.lessequal f1 f2)]
    | _ -> raise Not_implemented
  let hook_gt c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] -> [Bool (FR.greater f1 f2)]
    | _ -> raise Not_implemented
  let hook_ge c lbl sort config ff = match c with
      [Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] -> [Bool (FR.greaterequal f1 f2)]
    | _ -> raise Not_implemented
  let hook_precision c lbl sort config ff = match c with
      [Float (_,_,p)] :: [] -> [Int (Z.from_int p)]
    | _ -> raise Not_implemented
  let hook_exponentBits c lbl sort config ff = match c with
      [Float (_,e,_)] :: [] -> [Int (Z.from_int e)]
    | _ -> raise Not_implemented
  let hook_float2int c lbl sort config ff = match c with
      [Float (f,_,_)] :: [] -> [Int (FR.to_z_f f)]
    | _ -> raise Not_implemented
  let hook_int2float c lbl sort config ff = match c with
      [Int i] :: [Int prec] :: [Int exp] :: [] -> 
        [round_to_range(Float ((FR.from_z_prec (Z.to_int prec) GMP_RNDN i),(Z.to_int exp),(Z.to_int prec)))]
    | _ -> raise Not_implemented
  let hook_min c lbl sort config ff = raise Not_implemented
  let hook_max c lbl sort config ff = raise Not_implemented
  let hook_rem c lbl sort config ff = raise Not_implemented
  let hook_root c lbl sort config ff = raise Not_implemented
  let hook_sign c lbl sort config ff = raise Not_implemented
  let hook_significand c lbl sort config ff = raise Not_implemented
  let hook_atan2 c lbl sort config ff = raise Not_implemented
  let hook_exponent c lbl sort config ff = raise Not_implemented
end
