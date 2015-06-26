// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.java.kore.compile.ExpandMacros;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.Assoc;
import org.kframework.kore.AttCompare;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.ToKast;
import org.kframework.kore.compile.ConvertDataStructureToLookup;
import org.kframework.kore.compile.DeconstructIntegerAndFloatLiterals;
import org.kframework.kore.compile.GenerateSortPredicateRules;
import org.kframework.kore.compile.LiftToKSequence;
import org.kframework.kore.compile.NormalizeVariables;
import org.kframework.kore.compile.RewriteToTop;
import org.kframework.kore.compile.VisitKORE;
import org.kframework.main.GlobalOptions;
import org.kframework.mpfr.BigFloat;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Function1;
import scala.Tuple3;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;
import static scala.compat.java8.JFunction.*;

public class DefinitionToOcaml {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final GlobalOptions globalOptions;
    private final KompileOptions kompileOptions;
    private ExpandMacros expandMacros;

    public DefinitionToOcaml(KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions) {
        this.kem = kem;
        this.files = files;
        this.globalOptions = globalOptions;
        this.kompileOptions = kompileOptions;
    }
    public static final boolean ocamlopt = true;
    public static final boolean fastCompilation = false;
    public static final Pattern identChar = Pattern.compile("[A-Za-z0-9_]");

    public static final String kType = "t = kitem list\n" +
            " and kitem = KApply of klabel * t list\n" +
            "           | KToken of sort * string\n" +
            "           | InjectedKLabel of klabel\n" +
            "           | Map of sort * t m\n" +
            "           | List of sort * t list\n" +
            "           | Set of sort * s\n" +
            "           | Int of Z.t\n" +
            "           | Float of FR.t * int * int\n" +
            "           | String of string\n" +
            "           | Bool of bool\n" +
            "           | Bottom\n";

    public static final String TRUE = "(Bool true)";
    public static final String BOOL = encodeStringToIdentifier(Sort("Bool"));
    public static final String STRING = encodeStringToIdentifier(Sort("String"));
    public static final String INT = encodeStringToIdentifier(Sort("Int"));
    public static final String FLOAT = encodeStringToIdentifier(Sort("Float"));
    public static final String SET = encodeStringToIdentifier(Sort("Set"));

    public static final String prelude = "open Gmp\n" +
            "module type S =\n" +
            "sig\n" +
            "  type 'a m\n" +
            "  type s\n" +
            "  type " + kType +
            "  val compare : t -> t -> int\n" +
            "end \n" +
            "\n" +
            "\n" +
            "module rec K : (S with type 'a m = 'a Map.Make(K).t and type s = Set.Make(K).t)  = \n" +
            "struct\n" +
            "  module KMap = Map.Make(K)\n" +
            "  module KSet = Set.Make(K)\n" +
            "  type 'a m = 'a KMap.t\n" +
            "  and s = KSet.t\n" +
            "  and " + kType +
            "  let rec compare c1 c2 = match (c1, c2) with\n" +
            "    | [], [] -> 0\n" +
            "    | (hd1 :: tl1), (hd2 :: tl2) -> let v = compare_kitem hd1 hd2 in if v = 0 then compare tl1 tl2 else v\n" +
            "    | (hd1 :: tl1), _ -> -1\n" +
            "    | _ -> 1\n" +
            "  and compare_kitem c1 c2 = match (c1, c2) with\n" +
            "    | (KApply(kl1, k1)), (KApply(kl2, k2)) -> let v = Pervasives.compare kl1 kl2 in if v = 0 then compare_klist k1 k2 else v\n" +
            "    | (KToken(s1, st1)), (KToken(s2, st2)) -> let v = Pervasives.compare s1 s2 in if v = 0 then Pervasives.compare st1 st2 else v\n" +
            "    | (InjectedKLabel kl1), (InjectedKLabel kl2) -> Pervasives.compare kl1 kl2\n" +
            "    | (Map (s1,m1)), (Map (s2,m2)) -> let v = Pervasives.compare s1 s2 in if v = 0 then (KMap.compare) compare m1 m2 else v\n" +
            "    | (List (s1,l1)), (List (s2,l2)) -> let v = Pervasives.compare s1 s2 in if v = 0 then compare_klist l1 l2 else v\n" +
            "    | (Set (sort1,s1)), (Set (sort2,s2)) -> let v = Pervasives.compare sort1 sort2 in if v = 0 then (KSet.compare) s1 s2 else v\n" +
            "    | (Int i1), (Int i2) -> Z.compare i1 i2\n" +
            "    | (Float (f1,e1,p1)), (Float (f2,e2,p2)) -> let v = e2 - e1 in if v = 0 then let v2 = p2 - p1 in if v2 = 0 then FR.compare f1 f2 else v2 else v\n" +
            "    | (String s1), (String s2) -> Pervasives.compare s1 s2\n" +
            "    | (Bool b1), (Bool b2) -> if b1 = b2 then 0 else if b1 then -1 else 1\n" +
            "    | Bottom, Bottom -> 0\n" +
            "    | KApply(_, _), _ -> -1\n" +
            "    | _, KApply(_, _) -> 1\n" +
            "    | KToken(_, _), _ -> -1\n" +
            "    | _, KToken(_, _) -> 1\n" +
            "    | InjectedKLabel(_), _ -> -1\n" +
            "    | _, InjectedKLabel(_) -> 1\n" +
            "    | Map(_), _ -> -1\n" +
            "    | _, Map(_) -> 1\n" +
            "    | List(_), _ -> -1\n" +
            "    | _, List(_) -> 1\n" +
            "    | Set(_), _ -> -1\n" +
            "    | _, Set(_) -> 1\n" +
            "    | Int(_), _ -> -1\n" +
            "    | _, Int(_) -> 1\n" +
            "    | Float(_), _ -> -1\n" +
            "    | _, Float(_) -> 1\n" +
            "    | String(_), _ -> -1\n" +
            "    | _, String(_) -> 1\n" +
            "    | Bool(_), _ -> -1\n" +
            "    | _, Bool(_) -> 1\n" +
            "  and compare_klist c1 c2 = match (c1, c2) with\n" +
            "    | [], [] -> 0\n" +
            "    | (hd1 :: tl1), (hd2 :: tl2) -> let v = compare hd1 hd2 in if v = 0 then compare_klist tl1 tl2 else v\n" +
            "    | (hd1 :: tl1), _ -> -1\n" +
            "    | _ -> 1\n" +
            "end\n\n" +
            "module KMap = Map.Make(K)\n" +
            "module KSet = Set.Make(K)\n" +
            "\n" +
            "open K\n" +
            "type k = K.t" +
            "\n" +
            "exception Stuck of k\n" +
            "module GuardElt = struct\n" +
            "  type t = Guard of int\n" +
            "  let compare c1 c2 = match c1 with Guard(i1) -> match c2 with Guard(i2) -> i2 - i1\n" +
            "end\n" +
            "module Guard = Set.Make(GuardElt)\n" +
            "let freshCounter : Z.t ref = ref Z.zero\n" +
            "let eq k1 k2 = k1 = k2\n" +
            "let isTrue(c: k) : bool = match c with\n" +
            "| ([" + TRUE + "]) -> true\n" +
            "| _ -> false\n" +
            "let rec list_range (c: k list * int * int) : k list = match c with\n" +
            "| (_, 0, 0) -> []\n" +
            "| (head :: tail, 0, len) -> head :: list_range(tail, 0, len - 1)\n" +
            "| (_ :: tail, n, len) -> list_range(tail, n - 1, len)\n" +
            "| ([], _, _) -> raise(Failure \"list_range\")\n" +
            "let float_to_string (f: FR.t) : string = if FR.is_nan f then \"NaN\" else if FR.is_inf f then if FR.sgn f > 0 then \"Infinity\" else \"-Infinity\" else FR.to_string f\n" +
            "let rec print_klist(c: k list) : string = match c with\n" +
            "| [] -> \".KList\"\n" +
            "| e::[] -> print_k(e)\n" +
            "| e1::e2::l -> print_k(e1) ^ \", \" ^ print_klist(e2::l)\n" +
            "and print_k(c: k) : string = match c with\n" +
            "| [] -> \".K\"\n" +
            "| e::[] -> print_kitem(e)\n" +
            "| e1::e2::l -> print_kitem(e1) ^ \" ~> \" ^ print_k(e2::l)\n" +
            "and print_kitem(c: kitem) : string = match c with\n" +
            "| KApply(klabel, klist) -> print_klabel(klabel) ^ \"(\" ^ print_klist(klist) ^ \")\"\n" +
            "| KToken(sort, s) -> \"#token(\\\"\" ^ (String.escaped s) ^ \"\\\", \\\"\" ^ print_sort(sort) ^ \"\\\")\"\n" +
            "| InjectedKLabel(klabel) -> \"#klabel(\" ^ print_klabel(klabel) ^ \")\"\n" +
            "| Bool(b) -> print_kitem(KToken(" + BOOL + ", string_of_bool(b)))\n" +
            "| String(s) -> print_kitem(KToken(" + STRING + ", \"\\\"\" ^ (String.escaped s) ^ \"\\\"\"))\n" +
            "| Int(i) -> print_kitem(KToken(" + INT + ", Z.to_string(i)))\n" +
            "| Float(f,_,_) -> print_kitem(KToken(" + FLOAT + ", float_to_string(f)))\n" +
            "| Bottom -> \"`#Bottom`(.KList)\"\n" +
            "| List(_,l) -> List.fold_left (fun s k -> \"`_List_`(`ListItem`(\" ^ print_k(k) ^ \"),\" ^ s ^ \")\") \"`.List`(.KList)\" l\n" +
            "| Set(_,s) -> KSet.fold (fun k s -> \"`_Set_`(`SetItem`(\" ^ print_k(k) ^ \"), \" ^ s ^ \")\") s \"`.Set`(.KList)\"\n" +
            "| Map(_,m) -> KMap.fold (fun k v s -> \"`_Map_`(`_|->_`(\" ^ print_k(k) ^ \", \" ^ print_k(v) ^ \"), \" ^ s ^ \")\") m \"`.Map`(.KList)\"\n" +
            "module Subst = Map.Make(String)\n" +
            "let print_subst (out: out_channel) (c: k Subst.t) : unit = \n" +
            "  output_string out \"1\\n\"; Subst.iter (fun v k -> output_string out (v ^ \"\\n\" ^ (print_k k) ^ \"\\n\")) c\n" +
            "let emin (exp: int) (prec: int) : int = (- (1 lsl exp - 1)) + 4 - prec\n" +
            "let emax (exp: int) : int = 1 lsl exp - 1\n" +
            "let round_to_range (c: kitem) : kitem = match c with Float(f,e,p) -> let (cr, t) = (FR.check_range p GMP_RNDN (emin e p) (emax e) f) in Float((FR.subnormalize cr t GMP_RNDN),e,p)\n" +
            "let curr_fd : Z.t ref = ref (Z.of_int 3)\n" +
            "let file_descriptors = let m = Hashtbl.create 5 in Hashtbl.add m (Z.from_int 0) Unix.stdin; Hashtbl.add m (Z.from_int 1) Unix.stdout; Hashtbl.add m (Z.from_int 2) Unix.stderr; m\n" +
            "let default_file_perm = let v = Unix.umask 0 in Unix.umask v; (lnot v) land 0o777\n" +
            "let convert_open_flags (s: string) : Unix.open_flag list = match s with \"r\" -> [Unix.O_RDONLY] | \"w\" -> [Unix.O_WRONLY] | \"rw\" -> [Unix.O_RDWR]\n";

    public static final String postlude = "let run c n=\n" +
            "  try let rec go c n = if n = 0 then c else go (step c) (n - 1)\n" +
            "      in go c n\n" +
            "  with Stuck c' -> c'\n";

    public static final ImmutableMap<String, String> hooks;
    public static final ImmutableMap<String, Function<String, String>> sortHooks;
    public static final ImmutableMap<String, Function<Sort, String>> sortVarHooks;
    public static final ImmutableMap<String, String> predicateRules;

    static {
        ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
        builder.put("Map:_|->_", "k1 :: k2 :: [] -> [Map (sort,(KMap.singleton k1 k2))]");
        builder.put("Map:.Map", "[] -> [Map (sort,KMap.empty)]");
        builder.put("Map:__", "([Map (s1,k1)]) :: ([Map (s2,k2)]) :: [] when (s1 = s2) -> [Map (s1,(KMap.merge (fun k a b -> match a, b with None, None -> None | None, Some v | Some v, None -> Some v | Some v1, Some v2 when v1 = v2 -> Some v1) k1 k2))]");
        builder.put("Map:lookup", "[Map (_,k1)] :: k2 :: [] -> (try KMap.find k2 k1 with Not_found -> [Bottom])");
        builder.put("Map:update", "[Map (s,k1)] :: k :: v :: [] -> [Map (s,(KMap.add k v k1))]");
        builder.put("Map:remove", "[Map (s,k1)] :: k2 :: [] -> [Map (s,(KMap.remove k2 k1))]");
        builder.put("Map:keys", "[Map (_,k1)] :: [] -> [Set (" + SET + ",(KMap.fold (fun k v -> KSet.add k) k1 KSet.empty))]");
        builder.put("Map:values", "[Map (_,k1)] :: [] -> [Set (" + SET + ",(KMap.fold (fun key -> KSet.add) k1 KSet.empty))]");
        builder.put("Map:choice", "[Map (_,k1)] :: [] -> match KMap.choose k1 with (k, _) -> k");
        builder.put("Map:updateAll", "([Map (s1,k1)]) :: ([Map (s2,k2)]) :: [] when (s1 = s2) -> [Map (s1,(KMap.merge (fun k a b -> match a, b with None, None -> None | None, Some v | Some v, None | Some _, Some v -> Some v) k1 k2))]");
        builder.put("Set:in", "k1 :: [Set (_,k2)] :: [] -> [Bool (KSet.mem k1 k2)]");
        builder.put("Set:.Set", "[] -> [Set (sort,KSet.empty)]");
        builder.put("Set:SetItem", "k :: [] -> [Set (sort,(KSet.singleton k))]");
        builder.put("Set:__", "[Set (sort1,s1)] :: [Set (sort2,s2)] :: [] when (sort1 = sort2) -> [Set (sort1,(KSet.union s1 s2))]");
        builder.put("Set:difference", "[Set (s1,k1)] :: [Set (s2,k2)] :: [] when (s1 = s2) -> [Set (s1,(KSet.diff k1 k2))]");
        builder.put("Set:inclusion", "[Set (s1,k1)] :: [Set (s2,k2)] :: [] when (s1 = s2) -> [Bool (KSet.subset k1 k2)]");
        builder.put("Set:intersection", "[Set (s1,k1)] :: [Set (s2,k2)] :: [] when (s1 = s2) -> [Set (s1,(KSet.inter k1 k2))]");
        builder.put("Set:choice", "[Set (_,k1)] :: [] -> KSet.choose k1");
        builder.put("List:.List", "[] -> [List (sort,[])]");
        builder.put("List:ListItem", "k :: [] -> [List (sort,[k])]");
        builder.put("List:__", "[List (s1,l1)] :: [List (s2,l2)] :: [] when (s1 = s2) -> [List (s1,(l1 @ l2))]");
        builder.put("List:in", "k1 :: [List (_,k2)] :: [] -> [Bool (List.mem k1 k2)]");
        builder.put("List:get", "[List (_,l1)] :: [Int i] :: [] -> let i = Z.to_int i in (try if i >= 0 then List.nth l1 i else List.nth l1 ((List.length l1) + i) with Failure \"nth\" -> [Bottom] | Invalid_argument \"List.nth\" -> [Bottom])");
        builder.put("List:range", "[List (s,l1)] :: [Int i1] :: [Int i2] :: [] -> (try [List (s,(list_range (l1, (Z.to_int i1), (List.length(l1) - (Z.to_int i2) - (Z.to_int i1)))))] with Failure \"list_range\" -> [Bottom])");
        builder.put("Collection:size", "[List (_,l)] :: [] -> [Int (Z.of_int (List.length l))] " +
                "| [Map (_,m)] :: [] -> [Int (Z.of_int (KMap.cardinal m))] " +
                "| [Set (_,s)] :: [] -> [Int (Z.of_int (KSet.cardinal s))]");
        builder.put("MetaK:#sort", "[KToken (sort, s)] :: [] -> [String (print_sort(sort))] " +
                "| [Int _] :: [] -> [String \"Int\"] " +
                "| [String _] :: [] -> [String \"String\"] " +
                "| [Bool _] :: [] -> [String \"Bool\"] " +
                "| [Map (s,_)] :: [] -> [String (print_sort s)] " +
                "| [List (s,_)] :: [] -> [String (print_sort s)] " +
                "| [Set (s,_)] :: [] -> [String (print_sort s)] " +
                "| _ -> [String \"\"]");
        builder.put("MetaK:getKLabel", "[KApply (lbl, _)] :: [] -> [InjectedKLabel lbl] | _ -> [Bottom]");
        builder.put("MetaK:#configuration", "[] -> config");
        builder.put("#K-EQUAL:_==K_", "k1 :: k2 :: [] -> [Bool (eq k1 k2)]");
        builder.put("#IO:#close", "[Int i] :: [] -> Unix.close (Hashtbl.find file_descriptors i); []");
        builder.put("#IO:#getc", "[Int i] :: [] -> let b = Bytes.create 1 in Unix.read (Hashtbl.find file_descriptors i) b 0 1; [Int (Z.from_int (Char.code (Bytes.get b 0)))]");
        builder.put("#IO:#open", "[String path] :: [String flags] :: [] -> let fd = Unix.openfile path (convert_open_flags flags) default_file_perm in " +
                "let fd_int = !curr_fd in Hashtbl.add file_descriptors fd_int fd; " +
                "curr_fd := (Z.add fd_int Z.one); " +
                "[Int fd_int]");
        builder.put("#IO:#putc", "[Int fd] :: [Int c] :: [] -> Unix.write (Hashtbl.find file_descriptors fd) (Bytes.make 1 (Char.chr (Z.to_int c))) 0 1; []");
        builder.put("#IO:#read", "[Int fd] :: [Int len] :: [] -> let l = (Z.to_int len) in let b = Bytes.create l in Unix.read (Hashtbl.find file_descriptors fd) b 0 l; [String (Bytes.to_string b)]");
        builder.put("#IO:#seek", "[Int fd] :: [Int off] :: [] -> let o = (Z.to_int off) in Unix.lseek (Hashtbl.find file_descriptors fd) o Unix.SEEK_SET; []");
        builder.put("#IO:#tell", "[Int fd] :: [] -> [Int (Z.of_int (Unix.lseek (Hashtbl.find file_descriptors fd) 0 Unix.SEEK_CUR))]");
        builder.put("#IO:#write", "[Int fd] :: [String s] :: [] -> let b = Bytes.of_string s in Unix.write (Hashtbl.find file_descriptors fd) b 0 (Bytes.length b); []");
        builder.put("#BOOL:_andBool_", "[Bool b1] :: [Bool b2] :: [] -> [Bool (b1 && b2)]");
        builder.put("#BOOL:_andThenBool_", "[Bool b1] :: [Bool b2] :: [] -> [Bool (b1 && b2)]");
        builder.put("#BOOL:_orBool_", "[Bool b1] :: [Bool b2] :: [] -> [Bool (b1 || b2)]");
        builder.put("#BOOL:_orElseBool_", "[Bool b1] :: [Bool b2] :: [] -> [Bool (b1 || b2)]");
        builder.put("#BOOL:notBool_", "[Bool b1] :: [] -> [Bool (not b1)]");
        builder.put("#STRING:_+String_", "[String s1] :: [String s2] :: [] -> [String (s1 ^ s2)]");
        builder.put("#STRING:_<String_", "[String s1] :: [String s2] :: [] -> [Bool ((String.compare s1 s2) < 0)]");
        builder.put("#STRING:_<=String_", "[String s1] :: [String s2] :: [] -> [Bool ((String.compare s1 s2) <= 0)]");
        builder.put("#STRING:_>String_", "[String s1] :: [String s2] :: [] -> [Bool ((String.compare s1 s2) > 0)]");
        builder.put("#STRING:_>=String_", "[String s1] :: [String s2] :: [] -> [Bool ((String.compare s1 s2) >= 0)]");
        builder.put("#STRING:chrChar", "[Int i] :: [] -> [String (String.make 1 (Char.chr (Z.to_int i)))]");
        builder.put("#STRING:findString", "[String s1] :: [String s2] :: [Int i] :: [] -> try [Int (Z.of_int (Str.search_forward (Str.regexp_string s2) s1 (Z.to_int i)))] with Not_found -> [Int (Z.of_int (-1))]");
        builder.put("#STRING:rfindString", "[String s1] :: [String s2] :: [Int i] :: [] -> try [Int (Z.of_int (Str.search_backward (Str.regexp_string s2) s1 (Z.to_int i)))] with Not_found -> [Int (Z.of_int (-1))]");
        builder.put("#STRING:lengthString", "[String s] :: [] -> [Int (Z.of_int (String.length s))]");
        builder.put("#STRING:substrString", "[String s] :: [Int i1] :: [Int i2] :: [] -> [String (String.sub s (Z.to_int i1) (Z.to_int (Z.sub i2 i1)))]");
        builder.put("#STRING:ordChar", "[String s] :: [] -> [Int (Z.of_int (Char.code (String.get s 0)))]");
        builder.put("#INT:_%Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.tdiv_r a b)]");
        builder.put("#INT:_+Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.add a b)]");
        builder.put("#INT:_<=Int_", "[Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) <= 0)]");
        builder.put("#INT:_&Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.band a b)]");
        builder.put("#INT:_*Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.mul a b)]");
        builder.put("#INT:_-Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.sub a b)]");
        builder.put("#INT:_/Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.tdiv_q a b)]");
        builder.put("#INT:_<<Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.mul_2exp a (Z.to_int b))]");
        builder.put("#INT:_<Int_", "[Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) < 0)]");
        builder.put("#INT:_>=Int_", "[Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) >= 0)]");
        builder.put("#INT:_>>Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.fdiv_q_2exp a (Z.to_int b))]");
        builder.put("#INT:_>Int_", "[Int a] :: [Int b] :: [] -> [Bool ((Z.compare a b) > 0)]");
        builder.put("#INT:_^Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.pow_ui a (Z.to_int b))]");
        builder.put("#INT:_xorInt_", "[Int a] :: [Int b] :: [] -> [Int (Z.bxor a b)]");
        builder.put("#INT:_|Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.bior a b)]");
        builder.put("#INT:absInt", "[Int a] :: [] -> [Int (Z.abs a)]");
        builder.put("#INT:maxInt", "[Int a] :: [Int b] :: [] -> [Int (Z.max a b)]");
        builder.put("#INT:minInt", "[Int a] :: [Int b] :: [] -> [Int (Z.min a b)]");
        builder.put("#FLOAT:isNaN", "[Float (f,_,_)] :: [] -> [Bool (FR.is_nan f)]");
        builder.put("#FLOAT:maxValue", "[Int prec] :: [Int exp] :: [] -> " +
                "[round_to_range(Float ((FR.nexttoward (FR.from_string_prec_base (Z.to_int prec) GMP_RNDN 10 \"inf\") FR.zero),(Z.to_int exp),(Z.to_int prec)))]");
        builder.put("#FLOAT:abs", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.abs_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:acos", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.acos_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:asin", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.asin_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:atan", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.atan_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:cos", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.cos_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:sin", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.sin_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:tan", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.tan_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:exp", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.exp_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:neg", "[Float (f,e,p)] :: [] -> [round_to_range(Float ((FR.neg_prec p GMP_RNDN f),e,p))]");
        builder.put("#FLOAT:add", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.add_prec p1 GMP_RNDN f1 f2),e1,p1))]");
        builder.put("#FLOAT:sub", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.sub_prec p1 GMP_RNDN f1 f2),e1,p1))]");
        builder.put("#FLOAT:mul", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.mul_prec p1 GMP_RNDN f1 f2),e1,p1))]");
        builder.put("#FLOAT:div", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [round_to_range(Float ((FR.div_prec p1 GMP_RNDN f1 f2),e1,p1))]");
        builder.put("#FLOAT:eq", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [Bool (FR.equal f1 f2)]");
        builder.put("#FLOAT:lt", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [Bool (FR.less f1 f2)]");
        builder.put("#FLOAT:le", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [Bool (FR.lessequal f1 f2)]");
        builder.put("#FLOAT:gt", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [Bool (FR.greater f1 f2)]");
        builder.put("#FLOAT:ge", "[Float (f1,e1,p1)] :: [Float (f2,e2,p2)] :: [] when e1 = e2 && p1 = p2 -> [Bool (FR.greaterequal f1 f2)]");
        builder.put("#FLOAT:precision", "[Float (_,_,p)] :: [] -> [Int (Z.from_int p)]");
        builder.put("#FLOAT:exponentBits", "[Float (_,e,_)] :: [] -> [Int (Z.from_int e)]");
        builder.put("#CONVERSION:float2Int", "[Float (f,_,_)] :: [] -> [Int (FR.to_z_f f)]");
        builder.put("#CONVERSION:int2Float", "[Int i] :: [Int prec] :: [Int exp] :: [] -> [round_to_range(Float ((FR.from_z_prec (Z.to_int prec) GMP_RNDN i),(Z.to_int exp),(Z.to_int prec)))]");
        builder.put("#CONVERSION:int2string", "[Int i] :: [] -> [String (Z.to_string i)]");
        builder.put("#CONVERSION:string2int", "[String s] :: [] -> [Int (Z.from_string s)]");
        builder.put("#CONVERSION:string2base", "[String s] :: [Int i] :: [] -> [Int (Z.from_string_base (Z.to_int i) s)]");
        builder.put("#CONVERSION:base2string", "[Int i] :: [Int base] :: [] -> [String (Z.to_string_base (Z.to_int base) i)]");
        builder.put("#FRESH:fresh", "[String sort] :: [] -> let res = freshFunction sort config !freshCounter in freshCounter := Z.add !freshCounter Z.one; res");
        hooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, Function<String, String>> builder = ImmutableMap.builder();
        builder.put("#BOOL", s -> "(Bool " + s + ")");
        builder.put("#INT", s -> "(Int (Z.from_string \"" + s + "\"))");
        builder.put("#FLOAT", s -> {
            Pair<BigFloat, Integer> f = FloatBuiltin.parseKFloat(s);
            return "(round_to_range(Float ((FR.from_string_prec_base " + f.getLeft().precision() + " GMP_RNDN 10 \"" + f.getLeft().toString() + "\"), " + f.getRight() + ", " + f.getLeft().precision() + ")))";
        });
        builder.put("#STRING", s -> "(String " + StringUtil.enquoteCString(StringUtil.unquoteKString(StringUtil.unquoteKString("\"" + s + "\""))) + ")");
        sortHooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, Function<Sort, String>> builder = ImmutableMap.builder();
        builder.put("#BOOL", s -> "Bool _");
        builder.put("#INT", s -> "Int _");
        builder.put("#FLOAT", s -> "Float _");
        builder.put("#STRING", s -> "String _");
        builder.put("List", s -> "List (" + encodeStringToIdentifier(s) + ",_)");
        builder.put("Map", s -> "Map (" + encodeStringToIdentifier(s) + ",_)");
        builder.put("Set", s -> "Set (" + encodeStringToIdentifier(s) + ",_)");
        sortVarHooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
        builder.put("org.kframework.kore.K", "k1 :: [] -> [Bool true]");
        builder.put("org.kframework.kore.KItem", "[k1] :: [] -> [Bool true]");
        builder.put("#INT", "[Int _] :: [] -> [Bool true]");
        builder.put("#FLOAT", "[Float _] :: [] -> [Bool true]");
        builder.put("#STRING", "[String _] :: [] -> [Bool true]");
        builder.put("#BOOL", "[Bool _] :: [] -> [Bool true]");
        builder.put("Map", "[Map (s,_)] :: [] when (s = pred_sort) -> [Bool true]");
        builder.put("Set", "[Set (s,_)] :: [] when (s = pred_sort) -> [Bool true]");
        builder.put("List", "[List (s,_)] :: [] when (s = pred_sort) -> [Bool true]");
        predicateRules = builder.build();
    }


    private Module mainModule;
    private Map<KLabel, KLabel> collectionFor;

    public String convert(CompiledDefinition def) {
        Function1<Module, Module> generatePredicates = func(new GenerateSortPredicateRules(def.kompiledDefinition)::gen);
        ModuleTransformer convertLookups = ModuleTransformer.fromSentenceTransformer(new ConvertDataStructureToLookup(def.executionModule(), true)::convert, "convert data structures to lookups");
        ModuleTransformer liftToKSequence = ModuleTransformer.fromSentenceTransformer(new LiftToKSequence()::lift, "lift K into KSequence");
        this.expandMacros = new ExpandMacros(def.executionModule(), kem, files, globalOptions, kompileOptions);
        ModuleTransformer expandMacros = ModuleTransformer.fromSentenceTransformer(this.expandMacros::expand, "expand macro rules");
        ModuleTransformer deconstructInts = ModuleTransformer.fromSentenceTransformer(new DeconstructIntegerAndFloatLiterals()::convert, "remove matches on integer literals in left hand side");
        Function1<Module, Module> pipeline = deconstructInts
                .andThen(convertLookups)
                .andThen(expandMacros)
                .andThen(generatePredicates)
                .andThen(liftToKSequence);
        mainModule = pipeline.apply(def.executionModule());
        collectionFor = ConvertDataStructureToLookup.collectionFor(mainModule);
        return compile();
    }

    public Rule convert(Rule r) {
        Function1<Sentence, Sentence> convertLookups = func(new ConvertDataStructureToLookup(mainModule, true)::convert);
        Function1<Sentence, Sentence> liftToKSequence = func(new LiftToKSequence()::lift);
        Function1<Sentence, Sentence> deconstructInts = func(new DeconstructIntegerAndFloatLiterals()::convert);
        Function1<Sentence, Sentence> expandMacros = func(this.expandMacros::expand);
        return (Rule) deconstructInts
                .andThen(convertLookups)
                .andThen(expandMacros)
                .andThen(liftToKSequence)
                .apply(r);
    }

    Set<KLabel> functions;
    Set<KLabel> anywhereKLabels;

    public String execute(K k, int depth, String file) {
        StringBuilder sb = new StringBuilder();
        sb.append("open Def\nopen K\nopen Gmp\n");
        sb.append("let _ = let config = [Bottom] in let out = open_out " + StringUtil.enquoteCString(file) + " in output_string out (print_k(try(run(");
        convert(sb, true, new VarInfo(), false).apply(new LiftToKSequence().lift(expandMacros.expand(k)));
        sb.append(") (").append(depth).append(")) with Stuck c' -> c'))");
        return sb.toString();
    }

    public String match(K k, Rule r, String file) {
        StringBuilder sb = new StringBuilder();
        sb.append("open Def\nopen K\nopen Gmp\n");
        sb.append("let try_match (c: k) : k Subst.t = let config = c in match c with \n");
        convertFunction(Collections.singletonList(convert(r)), sb, "try_match", RuleType.PATTERN);
        sb.append("| _ -> raise(Stuck c)\n");
        sb.append("let _ = let config = [Bottom] in let out = open_out " + StringUtil.enquoteCString(file) + "in (try print_subst out (try_match(");
        convert(sb, true, new VarInfo(), false).apply(new LiftToKSequence().lift(expandMacros.expand(k)));
        sb.append(")) with Stuck c -> output_string out \"0\\n\")");
        return sb.toString();
    }

    private String compile() {
        StringBuilder sb = new StringBuilder();
        sb.append("type sort = \n");
        if (fastCompilation) {
            sb.append("Sort of string\n");
        } else {
            for (Sort s : iterable(mainModule.definedSorts())) {
                sb.append("|");
                encodeStringToIdentifier(sb, s);
                sb.append("\n");
            }
            if (!mainModule.definedSorts().contains(Sorts.String())) {
                sb.append("|SortString\n");
            }
            if (!mainModule.definedSorts().contains(Sorts.Float())) {
                sb.append("|SortFloat\n");
            }
        }
        sb.append("type klabel = \n");
        if (fastCompilation) {
            sb.append("KLabel of string\n");
        } else {
            for (KLabel label : iterable(mainModule.definedKLabels())) {
                sb.append("|");
                encodeStringToIdentifier(sb, label);
                sb.append("\n");
            }
        }
        sb.append("let print_sort(c: sort) : string = match c with \n");
        for (Sort s : iterable(mainModule.definedSorts())) {
            sb.append("|");
            encodeStringToIdentifier(sb, s);
            sb.append(" -> ");
            sb.append(StringUtil.enquoteCString(s.name()));
            sb.append("\n");
        }
        sb.append("let print_klabel(c: klabel) : string = match c with \n");
        for (KLabel label : iterable(mainModule.definedKLabels())) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            sb.append(StringUtil.enquoteCString(ToKast.apply(label)));
            sb.append("\n");
        }
        sb.append(prelude);
        SetMultimap<KLabel, Rule> functionRules = HashMultimap.create();
        ListMultimap<KLabel, Rule> anywhereRules = ArrayListMultimap.create();
        anywhereKLabels = new HashSet<>();
        for (Rule r : iterable(mainModule.rules())) {
            K left = RewriteToTop.toLeft(r.body());
            if (left instanceof KSequence) {
                KSequence kseq = (KSequence) left;
                if (kseq.items().size() == 1 && kseq.items().get(0) instanceof KApply) {
                    KApply kapp = (KApply) kseq.items().get(0);
                    if (mainModule.attributesFor().apply(kapp.klabel()).contains(Attribute.FUNCTION_KEY)) {
                        functionRules.put(kapp.klabel(), r);
                    }
                    if (r.att().contains("anywhere")) {
                        anywhereRules.put(kapp.klabel(), r);
                        anywhereKLabels.add(kapp.klabel());
                    }
                }
            }
        }
        functions = new HashSet<>(functionRules.keySet());
        for (Production p : iterable(mainModule.productions())) {
            if (p.att().contains(Attribute.FUNCTION_KEY)) {
                functions.add(p.klabel().get());
            }
        }

        String conn = "let rec ";
        for (KLabel functionLabel : functions) {
            sb.append(conn);
            String functionName = encodeStringToFunction(sb, functionLabel.name());
            sb.append(" (c: k list) (config: k) (guards: Guard.t) : k = let lbl = \n");
            encodeStringToIdentifier(sb, functionLabel);
            sb.append(" and sort = \n");
            encodeStringToIdentifier(sb, mainModule.sortFor().apply(functionLabel));
            String sortHook = "";
            if (mainModule.attributesFor().apply(functionLabel).contains(Attribute.PREDICATE_KEY)) {
                Sort sort = Sort(mainModule.attributesFor().apply(functionLabel).<String>get(Attribute.PREDICATE_KEY).get());
                sb.append(" and pred_sort = \n");
                encodeStringToIdentifier(sb, sort);
                if (mainModule.sortAttributesFor().contains(sort)) {
                    sortHook = mainModule.sortAttributesFor().apply(sort).<String>getOptional("hook").orElse("");
                }
            }
            sb.append(" in match c with \n");
            String hook = mainModule.attributesFor().apply(functionLabel).<String>getOptional(Attribute.HOOK_KEY).orElse("");
            if (hooks.containsKey(hook)) {
                sb.append("| ");
                sb.append(hooks.get(hook));
                sb.append("\n");
            } else if (!hook.isEmpty()) {
                kem.registerCompilerWarning("missing entry for hook " + hook);
            }
            if (predicateRules.containsKey(sortHook)) {
                sb.append("| ");
                sb.append(predicateRules.get(sortHook));
                sb.append("\n");
            }

            convertFunction( functionRules.get(functionLabel).stream().sorted(this::sortFunctionRules).collect(Collectors.toList()),
                    sb, functionName, RuleType.FUNCTION);
            sb.append("| _ -> raise (Stuck [KApply(lbl, c)])\n");
            conn = "and ";
        }
        for (KLabel functionLabel : anywhereKLabels) {
            sb.append(conn);
            String functionName = encodeStringToFunction(sb, functionLabel.name());
            sb.append(" (c: k list) (config: k) (guards: Guard.t) : k = let lbl = \n");
            encodeStringToIdentifier(sb, functionLabel);
            sb.append(" in match c with \n");
            convertFunction(anywhereRules.get(functionLabel), sb, functionName, RuleType.ANYWHERE);
            sb.append("| _ -> [KApply(lbl, c)]\n");
            conn = "and ";
        }

        sb.append("and freshFunction (sort: string) (config: k) (counter: Z.t) : k = match sort with \n");
        for (Sort sort : iterable(mainModule.freshFunctionFor().keys())) {
            sb.append("| \"").append(sort.name()).append("\" -> (");
            KLabel freshFunction = mainModule.freshFunctionFor().apply(sort);
            encodeStringToFunction(sb, freshFunction.name());
            sb.append(" ([Int counter] :: []) config Guard.empty)\n");
        }
        sb.append("and eval (c: kitem) (config: k) : k = match c with KApply(lbl, kl) -> match lbl with \n");
        for (KLabel label : Sets.union(functions, anywhereKLabels)) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            encodeStringToFunction(sb, label.name());
            sb.append(" kl config Guard.empty\n");
        }
        sb.append("| _ -> [c]");
        sb.append("let rec lookups_step (c: k) (config: k) (guards: Guard.t) : k = match c with \n");
        List<Rule> sortedRules = stream(mainModule.rules())
                .sorted((r1, r2) -> Boolean.compare(r2.att().contains("structural"), r1.att().contains("structural")))
                .filter(r -> !functionRules.values().contains(r) && !r.att().contains(Attribute.MACRO_KEY) && !r.att().contains(Attribute.ANYWHERE_KEY))
                .collect(Collectors.toList());
        Map<Boolean, List<Rule>> groupedByLookup = sortedRules.stream()
                .collect(Collectors.groupingBy(this::hasLookups));
        convert(groupedByLookup.get(true), sb, "lookups_step", RuleType.REGULAR);
        sb.append("| _ -> raise (Stuck c)\n");
        sb.append("let step (c: k) : k = let config = c in match c with \n");
        if (groupedByLookup.containsKey(false)) {
            for (Rule r : groupedByLookup.get(false)) {
                convert(r, sb, RuleType.REGULAR);
                if (fastCompilation) {
                    sb.append("| _ -> match c with \n");
                }
            }
        }
        sb.append("| _ -> lookups_step c c Guard.empty\n");
        sb.append(postlude);
        return sb.toString();
    }

    private void convertFunction(List<Rule> rules, StringBuilder sb, String functionName, RuleType type) {
        for (Rule r : rules) {
            if (hasLookups(r)) {
                convert(Collections.singletonList(r), sb, functionName, type);
            } else {
                convert(r, sb, type);
            }
            if (fastCompilation) {
                sb.append("| _ -> match c with \n");
            }
        }
    }

    private boolean hasLookups(Rule r) {
        class Holder { boolean b; }
        Holder h = new Holder();
        new VisitKORE() {
            @Override
            public Void apply(KApply k) {
                h.b |= isLookupKLabel(k);
                return super.apply(k);
            }
        }.apply(r.requires());
        return h.b;
    }

    private int sortFunctionRules(Rule a1, Rule a2) {
        return Boolean.compare(a1.att().contains("owise"), a2.att().contains("owise"));
    }

    private static void encodeStringToIdentifier(StringBuilder sb, KLabel name) {
        if (fastCompilation) {
            sb.append("KLabel(\"").append(name.name().replace("\"", "\\\"")).append("\")");
        } else {
            sb.append("Lbl");
            encodeStringToAlphanumeric(sb, name.name());
        }
    }

    private static void encodeStringToIdentifier(StringBuilder sb, Sort name) {
        if (fastCompilation) {
            sb.append("(Sort \"").append(name.name().replace("\"", "\\\"")).append("\")");
        } else {
            sb.append("Sort");
            encodeStringToAlphanumeric(sb, name.name());
        }
    }

    private static String encodeStringToIdentifier(Sort name) {
        StringBuilder sb = new StringBuilder();
        encodeStringToIdentifier(sb, name);
        return sb.toString();
    }


    private static String encodeStringToFunction(StringBuilder sb, String name) {
        StringBuilder sb2 = new StringBuilder();
        sb2.append("eval");
        encodeStringToAlphanumeric(sb2, name);
        sb.append(sb2);
        return sb2.toString();
    }

    private static long counter = 0;

    private static String encodeStringToVariable(String name) {
        StringBuilder sb2 = new StringBuilder();
        sb2.append("var");
        encodeStringToAlphanumeric(sb2, name);
        sb2.append("_");
        sb2.append(counter++);
        return sb2.toString();
    }

    private static void encodeStringToAlphanumeric(StringBuilder sb, String name) {
        boolean inIdent = true;
        for (int i = 0; i < name.length(); i++) {
            if (identChar.matcher(name).region(i, name.length()).lookingAt()) {
                if (!inIdent) {
                    inIdent = true;
                    sb.append("'");
                }
                sb.append(name.charAt(i));
            } else {
                if (inIdent) {
                    inIdent = false;
                    sb.append("'");
                }
                sb.append(String.format("%04x", (int) name.charAt(i)));
            }
        }
    }

    private static enum RuleType {
        FUNCTION, ANYWHERE, REGULAR, PATTERN
    }

    private static class VarInfo {
        final SetMultimap<KVariable, String> vars;
        final Map<KVariable, Sort> listVars;

        VarInfo() { this(HashMultimap.create(), new HashMap<>()); }

        VarInfo(VarInfo vars) {
            this(HashMultimap.create(vars.vars), new HashMap<>(vars.listVars));
        }

        VarInfo(SetMultimap<KVariable, String> vars, Map<KVariable, Sort> listVars) {
            this.vars = vars;
            this.listVars = listVars;
        }
    }

    private void convert(List<Rule> rules, StringBuilder sb, String functionName, RuleType ruleType) {
        NormalizeVariables t = new NormalizeVariables();
        Map<AttCompare, List<Rule>> grouping = rules.stream().collect(
                Collectors.groupingBy(r -> new AttCompare(t.normalize(RewriteToTop.toLeft(r.body())), "sort")));
        int ruleNum = 0;
        Map<Tuple3<AttCompare, KLabel, AttCompare>, List<Rule>> groupByFirstPrefix = new HashMap<>();
        for (Map.Entry<AttCompare, List<Rule>> entry : grouping.entrySet()) {
            AttCompare left = entry.getKey();
            groupByFirstPrefix.putAll(entry.getValue().stream()
                    .collect(Collectors.groupingBy(r -> {
                        KApply lookup = getLookup(r, 0);
                        if (lookup == null) return null;
                        //reconstruct the denormalization for this particular rule
                        K left2 = t.normalize(RewriteToTop.toLeft(r.body()));
                        K normal = t.normalize(t.applyNormalization(lookup.klist().items().get(1), left2));
                        return Tuple3.apply(left, lookup.klabel(), new AttCompare(normal, "sort"));
                    })));
        }
        List<Rule> owiseRules = new ArrayList<>();
        for (Map.Entry<Tuple3<AttCompare, KLabel, AttCompare>, List<Rule>> entry2 : groupByFirstPrefix.entrySet().stream().sorted((e1, e2) -> Integer.compare(e2.getValue().size(), e1.getValue().size())).collect(Collectors.toList())) {
            K left = entry2.getKey()._1().get();
            VarInfo globalVars = new VarInfo();
            sb.append("| ");
            convertLHS(sb, ruleType, left, globalVars);
            K lookup;
            sb.append(" when not (Guard.mem (GuardElt.Guard ").append(ruleNum).append(") guards)");
            if (entry2.getValue().size() == 1) {
                Rule r = entry2.getValue().get(0);
                convertComment(r, sb);

                //reconstruct the denormalization for this particular rule
                left = t.normalize(RewriteToTop.toLeft(r.body()));
                lookup = t.normalize(t.applyNormalization(getLookup(r, 0).klist().items().get(1), left));
                r = t.normalize(t.applyNormalization(r, left, lookup));

                List<Lookup> lookups = convertLookups(r.requires(), globalVars, functionName, ruleNum, false);
                String suffix = convertSideCondition(sb, r.requires(), globalVars, lookups, lookups.size() > 0);
                sb.append(" -> ");
                convertRHS(sb, ruleType, RewriteToTop.toRight(r.body()), globalVars, suffix);
                ruleNum++;

            } else {
                Lookup head = convertLookups(KApply(entry2.getKey()._2(),
                        KToken("dummy", Sort("Dummy")), entry2.getKey()._3().get()),
                        globalVars, functionName, ruleNum++, true).get(0);
                sb.append(head.prefix);
                for (Rule r : entry2.getValue()) {
                    if (indexesPoorly(r) || r.att().contains("owise")) {
                        owiseRules.add(r);
                    } else {
                        convertComment(r, sb);

                        //reconstruct the denormalization for this particular rule
                        left = t.normalize(RewriteToTop.toLeft(r.body()));
                        lookup = t.normalize(t.applyNormalization(getLookup(r, 0).klist().items().get(1), left));
                        r = t.normalize(t.applyNormalization(r, left, lookup));

                        VarInfo vars = new VarInfo(globalVars);
                        List<Lookup> lookups = convertLookups(r.requires(), vars, functionName, ruleNum, true);
                        sb.append(lookups.get(0).pattern);
                        lookups.remove(0);
                        sb.append(" when not (Guard.mem (GuardElt.Guard ").append(ruleNum).append(") guards)");
                        //sb.append("&& ((print_string \"trying rule " + ruleNum + "\\n\");true)");
                        String suffix = convertSideCondition(sb, r.requires(), vars, lookups, lookups.size() > 0);
                        sb.append(" -> ");
                        convertRHS(sb, ruleType, RewriteToTop.toRight(r.body()), vars, suffix);
                        ruleNum++;
                        if (fastCompilation) {
                            sb.append("| _ -> match e with \n");
                        }
                    }
                }
                sb.append(head.suffix);
                sb.append("\n");
            }
        }
        for (Rule r : owiseRules) {
            VarInfo globalVars = new VarInfo();
            sb.append("| ");
            convertLHS(sb, ruleType, RewriteToTop.toLeft(r.body()), globalVars);
            sb.append(" when not (Guard.mem (GuardElt.Guard ").append(ruleNum).append(") guards)");

            convertComment(r, sb);
            List<Lookup> lookups = convertLookups(r.requires(), globalVars, functionName, ruleNum, false);
            String suffix = convertSideCondition(sb, r.requires(), globalVars, lookups, lookups.size() > 0);
            sb.append(" -> ");
            convertRHS(sb, ruleType, RewriteToTop.toRight(r.body()), globalVars, suffix);
            ruleNum++;
        }
    }

    private boolean indexesPoorly(Rule r) {
        class Holder { boolean b; }
        Holder h = new Holder();
        VisitKORE visitor = new VisitKORE() {
            @Override
            public Void apply(KApply k) {
                if (k.klabel().name().equals("<k>")) {
                    if (k.klist().items().size() == 1) {
                        if (k.klist().items().get(0) instanceof KSequence) {
                            KSequence kCell = (KSequence) k.klist().items().get(0);
                            if (kCell.items().size() == 2 && kCell.items().get(1) instanceof KVariable) {
                                if (kCell.items().get(0) instanceof KVariable) {
                                    Sort s = Sort(kCell.items().get(0).att().<String>getOptional(Attribute.SORT_KEY).orElse(""));
                                    if (mainModule.sortAttributesFor().contains(s)) {
                                        String hook = mainModule.sortAttributesFor().apply(s).<String>getOptional("hook").orElse("");
                                        if (!sortVarHooks.containsKey(hook)) {
                                            h.b = true;
                                        }
                                    } else {
                                        h.b = true;
                                    }
                                } else if (kCell.items().get(0) instanceof KApply) {
                                    KApply kapp = (KApply) kCell.items().get(0);
                                    if (kapp.klabel() instanceof KVariable) {
                                        h.b = true;
                                    }
                                }
                            }
                        }
                    }
                }
                return super.apply(k);
            }
        };
        visitor.apply(RewriteToTop.toLeft(r.body()));
        visitor.apply(r.requires());
        return h.b;
    }

    private KApply getLookup(Rule r, int idx) {
        class Holder {
            int i = 0;
            KApply lookup;
        }
        Holder h = new Holder();
        new VisitKORE() {
            @Override
            public Void apply(KApply k) {
                if (h.i > idx)
                    return null;
                if (k.klabel().name().equals("#match")
                        || k.klabel().name().equals("#setChoice")
                        || k.klabel().name().equals("#mapChoice")) {
                    h.lookup = k;
                    h.i++;
                }
                return super.apply(k);
            }
        }.apply(r.requires());
        return h.lookup;
    }

    private void convert(Rule r, StringBuilder sb, RuleType type) {
        try {
            convertComment(r, sb);
            sb.append("| ");
            K left = RewriteToTop.toLeft(r.body());
            K right = RewriteToTop.toRight(r.body());
            K requires = r.requires();
            VarInfo vars = new VarInfo();
            convertLHS(sb, type, left, vars);
            String result = convert(vars);
            String suffix = "";
            if (!requires.equals(KSequence(BooleanUtils.TRUE)) || !result.equals("true")) {
                suffix = convertSideCondition(sb, requires, vars, Collections.emptyList(), true);
            }
            sb.append(" -> ");
            convertRHS(sb, type, right, vars, suffix);
        } catch (KEMException e) {
            e.exception.addTraceFrame("while compiling rule at " + r.att().getOptional(Source.class).map(Object::toString).orElse("<none>") + ":" + r.att().getOptional(Location.class).map(Object::toString).orElse("<none>"));
            throw e;
        }
    }

    private void convertLHS(StringBuilder sb, RuleType type, K left, VarInfo vars) {
        Visitor visitor = convert(sb, false, vars, false);
        if (type == RuleType.ANYWHERE || type == RuleType.FUNCTION) {
            KApply kapp = (KApply) ((KSequence) left).items().get(0);
            visitor.apply(kapp.klist().items(), true);
        } else {
            visitor.apply(left);
        }
    }

    private void convertComment(Rule r, StringBuilder sb) {
        sb.append("(* rule ");
        sb.append(ToKast.apply(r.body()));
        sb.append(" requires ");
        sb.append(ToKast.apply(r.requires()));
        sb.append(" ensures ");
        sb.append(ToKast.apply(r.ensures()));
        sb.append(" ");
        sb.append(r.att().toString());
        sb.append("*)\n");
    }

    private void convertRHS(StringBuilder sb, RuleType type, K right, VarInfo vars, String suffix) {
        if (type == RuleType.ANYWHERE) {
            sb.append("(match ");
        }
        if (type == RuleType.PATTERN) {
            for (KVariable var : vars.vars.keySet()) {
                sb.append("(Subst.add \"").append(var.name()).append("\" ");
                boolean isList = isList(var, false, true, vars);
                if (!isList) {
                    sb.append("[");
                }
                sb.append(vars.vars.get(var).iterator().next());
                if (!isList) {
                    sb.append("]");
                }
                sb.append(" ");
            }
            sb.append("Subst.empty");
            for (KVariable var : vars.vars.keySet()) {
                sb.append(")");
            }
        } else {
            convert(sb, true, vars, false).apply(right);
        }
        if (type == RuleType.ANYWHERE) {
            sb.append(" with [item] -> eval item config)");
        }
        sb.append(suffix);
        sb.append("\n");
    }

    private String convertSideCondition(StringBuilder sb, K requires, VarInfo vars, List<Lookup> lookups, boolean when) {
        String result;
        for (Lookup lookup : lookups) {
            sb.append(lookup.prefix).append(lookup.pattern);
        }
        result = convert(vars);
        sb.append(when ? " when " : " && ");
        convert(sb, true, vars, true).apply(requires);
        sb.append(" && (");
        sb.append(result);
        sb.append(")");
        return Lists.reverse(lookups).stream().map(l -> l.suffix).reduce("", String::concat);
    }

    private static class Holder { String reapply; boolean first; }

    private static class Lookup {
        final String prefix;
        final String pattern;
        final String suffix;

        public Lookup(String prefix, String pattern, String suffix) {
            this.prefix = prefix;
            this.pattern = pattern;
            this.suffix = suffix;
        }
    }

    private List<Lookup> convertLookups(K requires, VarInfo vars, String functionName, int ruleNum, boolean hasMultiple) {
        List<Lookup> results = new ArrayList<>();
        Holder h = new Holder();
        h.first = hasMultiple;
        h.reapply = "(" + functionName + " c config (Guard.add (GuardElt.Guard " + ruleNum + ") guards))";
        new VisitKORE() {
            @Override
            public Void apply(KApply k) {
                if (k.klabel().name().equals("#match")) {
                    if (k.klist().items().size() != 2) {
                        throw KEMException.internalError("Unexpected arity of lookup: " + k.klist().size(), k);
                    }
                    StringBuilder sb = new StringBuilder();
                    sb.append(" -> (let e = ");
                    convert(sb, true, vars, false).apply(k.klist().items().get(1));
                    sb.append(" in match e with \n");
                    sb.append("| [Bottom] -> ").append(h.reapply).append("\n");
                    String prefix = sb.toString();
                    sb = new StringBuilder();
                    sb.append("| ");
                    convert(sb, false, vars, false).apply(k.klist().items().get(0));
                    String pattern = sb.toString();
                    String suffix = "| _ -> " + h.reapply + ")";
                    results.add(new Lookup(prefix, pattern, suffix));
                    h.first = false;
                } else if (k.klabel().name().equals("#setChoice")) {
                    choose(k, "| [Set (_,collection)] -> let choice = (KSet.fold (fun e result -> ");
                } else if (k.klabel().name().equals("#mapChoice")) {
                    choose(k, "| [Map (_,collection)] -> let choice = (KMap.fold (fun e v result -> ");
                }
                return super.apply(k);
            }

            private void choose(KApply k, String choiceString) {
                if (k.klist().items().size() != 2) {
                    throw KEMException.internalError("Unexpected arity of choice: " + k.klist().size(), k);
                }
                StringBuilder sb = new StringBuilder();
                sb.append(" -> (match ");
                convert(sb, true, vars, false).apply(k.klist().items().get(1));
                sb.append(" with \n");
                sb.append(choiceString);
                if (h.first) {
                    sb.append("let rec stepElt = fun guards -> ");
                }
                sb.append("if (compare result [Bottom]) = 0 then (match e with ");
                String prefix = sb.toString();
                sb = new StringBuilder();
                String suffix2 = "| _ -> [Bottom]) else result" + (h.first ? " in stepElt Guard.empty" : "") + ") collection [Bottom]) in if (compare choice [Bottom]) = 0 then " + h.reapply + " else choice";
                String suffix = suffix2 + "| _ -> " + h.reapply + ")";
                if (h.first) {
                    h.reapply = "(stepElt (Guard.add (GuardElt.Guard " + ruleNum + ") guards))";
                } else {
                    h.reapply = "[Bottom]";
                }
                sb.append("| ");
                convert(sb, false, vars, false).apply(k.klist().items().get(0));
                String pattern = sb.toString();
                results.add(new Lookup(prefix, pattern, suffix));
                h.first = false;
            }
        }.apply(requires);
        return results;
    }

    private static String convert(VarInfo vars) {
        StringBuilder sb = new StringBuilder();
        for (Collection<String> nonLinearVars : vars.vars.asMap().values()) {
            if (nonLinearVars.size() < 2) {
                continue;
            }
            Iterator<String> iter = nonLinearVars.iterator();
            String last = iter.next();
            while (iter.hasNext()) {
                //handle nonlinear variables in pattern
                String next = iter.next();
                sb.append("(eq ");
                sb.append(last);
                sb.append(" ");
                sb.append(next);
                sb.append(")");
                last = next;
                sb.append(" && ");
            }
        }
        sb.append("true");
        return sb.toString();
    }

    private void applyVarRhs(KVariable v, StringBuilder sb, VarInfo vars) {
        if (vars.listVars.containsKey(v)) {
            sb.append("(List (");
            encodeStringToIdentifier(sb, vars.listVars.get(v));
            sb.append(", ");
            sb.append(vars.vars.get(v).iterator().next());
            sb.append("))");
        } else {
            sb.append(vars.vars.get(v).iterator().next());
        }
    }

    private void applyVarLhs(KVariable k, StringBuilder sb, VarInfo vars) {
        String varName = encodeStringToVariable(k.name());
        vars.vars.put(k, varName);
        Sort s = Sort(k.att().<String>getOptional(Attribute.SORT_KEY).orElse(""));
        if (mainModule.sortAttributesFor().contains(s)) {
            String hook = mainModule.sortAttributesFor().apply(s).<String>getOptional("hook").orElse("");
            if (sortVarHooks.containsKey(hook)) {
                sb.append("(");
                sb.append(sortVarHooks.get(hook).apply(s));
                sb.append(" as ").append(varName).append(")");
                return;
            }
        }
        sb.append(varName);
    }

    private Visitor convert(StringBuilder sb, boolean rhs, VarInfo vars, boolean useNativeBooleanExp) {
        return new Visitor(sb, rhs, vars, useNativeBooleanExp);
    }

    private class Visitor extends VisitKORE {
        private final StringBuilder sb;
        private final boolean rhs;
        private final VarInfo vars;
        private final boolean useNativeBooleanExp;

        public Visitor(StringBuilder sb, boolean rhs, VarInfo vars, boolean useNativeBooleanExp) {
            this.sb = sb;
            this.rhs = rhs;
            this.vars = vars;
            this.useNativeBooleanExp = useNativeBooleanExp;
            this.inBooleanExp = useNativeBooleanExp;
        }

        private boolean inBooleanExp;

        @Override
        public Void apply(KApply k) {
            if (k.klabel() instanceof KVariable && rhs) {
                sb.append("(eval (");
                applyKLabel(k);
                sb.append(") config)");
                return null;
            }
            if (isLookupKLabel(k)) {
                apply(BooleanUtils.TRUE);
            } else if (k.klabel().name().equals("#KToken")) {
                //magic down-ness
                sb.append("KToken (");
                Sort sort = Sort(((KToken) ((KSequence) k.klist().items().get(0)).items().get(0)).s());
                apply(sort);
                sb.append(", ");
                apply(((KSequence) k.klist().items().get(1)).items().get(0));
                sb.append(")");
            } else if (functions.contains(k.klabel()) || (anywhereKLabels.contains(k.klabel()) && rhs)) {
                applyFunction(k);
            } else {
                applyKLabel(k);
            }
            return null;
        }

        public void applyKLabel(KApply k) {
            sb.append("KApply (");
            apply(k.klabel());
            sb.append(", ");
            apply(k.klist().items(), true);
            sb.append(")");
        }

        public void applyFunction(KApply k) {
            boolean stack = inBooleanExp;
            String hook = mainModule.attributesFor().apply(k.klabel()).<String>getOptional(Attribute.HOOK_KEY).orElse("");
            // use native &&, ||, not where possible
            if (useNativeBooleanExp && (hook.equals("#BOOL:_andBool_") || hook.equals("#BOOL:_andThenBool_"))) {
                assert k.klist().items().size() == 2;
                if (!stack) {
                    sb.append("[Bool ");
                }
                inBooleanExp = true;
                sb.append("(");
                apply(k.klist().items().get(0));
                sb.append(") && (");
                apply(k.klist().items().get(1));
                sb.append(")");
                if (!stack) {
                    sb.append("]");
                }
            } else if (useNativeBooleanExp && (hook.equals("#BOOL:_orBool_") || hook.equals("#BOOL:_orElseBool_"))) {
                assert k.klist().items().size() == 2;
                if (!stack) {
                    sb.append("[Bool ");
                }
                inBooleanExp = true;
                sb.append("(");
                apply(k.klist().items().get(0));
                sb.append(") || (");
                apply(k.klist().items().get(1));
                sb.append(")");
                if (!stack) {
                    sb.append("]");
                }
            } else if (useNativeBooleanExp && hook.equals("#BOOL:notBool_")) {
                assert k.klist().items().size() == 1;
                if (!stack) {
                    sb.append("[Bool ");
                }
                inBooleanExp = true;
                sb.append("(not (");
                apply(k.klist().items().get(0));
                sb.append("))");
                if (!stack) {
                    sb.append("]");
                }
            } else {
                if (collectionFor.containsKey(k.klabel()) && !rhs) {
                    KLabel collectionLabel = collectionFor.get(k.klabel());
                    Att attr = mainModule.attributesFor().apply(collectionLabel);
                    if (attr.contains(Attribute.ASSOCIATIVE_KEY)
                            && !attr.contains(Attribute.COMMUTATIVE_KEY)
                            && !attr.contains(Attribute.IDEMPOTENT_KEY)) {
                        // list
                        sb.append("(List (");
                        encodeStringToIdentifier(sb, mainModule.sortFor().apply(collectionLabel));
                        sb.append(", ");
                        List<K> components = Assoc.flatten(collectionLabel, Collections.singletonList(new LiftToKSequence().lower(k)), mainModule);
                        LiftToKSequence lift = new LiftToKSequence();
                        boolean frame = false;
                        for (K component : components) {
                            if (component instanceof KVariable) {
                                // don't want to encode this variable as a List kitem, so we skip the apply method.
                                KVariable var = (KVariable)component;
                                String varName = encodeStringToVariable(var.name());
                                vars.vars.put(var, varName);
                                vars.listVars.put(var, mainModule.sortFor().apply(collectionLabel));
                                sb.append(varName);
                                frame = true;
                            } else if (component instanceof KApply) {
                                KApply kapp = (KApply) component;
                                boolean needsWrapper = false;
                                if (kapp.klabel().equals(KLabel(attr.<String>get("element").get()))
                                        || (needsWrapper = kapp.klabel().equals(KLabel(attr.<String>get("wrapElement").get())))) {
                                    if (kapp.klist().size() != 1 && !needsWrapper) {
                                        throw KEMException.internalError("Unexpected arity of list element: " + kapp.klist().size(), kapp);
                                    }
                                    if (needsWrapper) {
                                        apply(lift.lift(kapp));
                                    } else {
                                        apply(lift.lift(kapp.klist().items().get(0)));
                                    }
                                    sb.append(" :: ");
                                } else {
                                    throw KEMException.internalError("Unexpected term in list, not a list element.", kapp);
                                }
                            } else {
                                assert false;
                            }
                        }
                        if (!frame) {
                            sb.append("[]");
                        }
                        sb.append("))");
                        return;
                    }
                }
                if (mainModule.attributesFor().apply(k.klabel()).contains(Attribute.PREDICATE_KEY)) {
                    Sort s = Sort(mainModule.attributesFor().apply(k.klabel()).<String>get(Attribute.PREDICATE_KEY).get());
                    if (mainModule.sortAttributesFor().contains(s)) {
                        String hook2 = mainModule.sortAttributesFor().apply(s).<String>getOptional("hook").orElse("");
                        if (sortVarHooks.containsKey(hook2)) {
                            if (k.klist().items().size() == 1) {
                                KSequence item = (KSequence) k.klist().items().get(0);
                                if (item.items().size() == 1 &&
                                        vars.vars.containsKey(item.items().get(0))) {
                                    Optional<String> varSort = item.items().get(0).att().<String>getOptional(Attribute.SORT_KEY);
                                    if (varSort.isPresent() && varSort.get().equals(s.name())) {
                                        // this has been subsumed by a structural check on the builtin data type
                                        apply(BooleanUtils.TRUE);
                                        return;
                                    }
                                }
                            }
                        }
                    }
                    if (s.equals(Sorts.KItem()) && k.klist().items().size() == 1) {
                        if (k.klist().items().get(0) instanceof KSequence) {
                            KSequence item = (KSequence) k.klist().items().get(0);
                            if (item.items().size() == 1) {
                                apply(BooleanUtils.TRUE);
                                return;
                            }
                        }
                    }
                }
                if (stack) {
                    sb.append("(isTrue ");
                }
                inBooleanExp = false;
                sb.append("(");
                encodeStringToFunction(sb, k.klabel().name());
                sb.append("(");
                apply(k.klist().items(), true);
                sb.append(") config Guard.empty)");
                if (stack) {
                    sb.append(")");
                }
            }
            inBooleanExp = stack;
        }

        @Override
        public Void apply(KRewrite k) {
            throw new AssertionError("unexpected rewrite");
        }

        @Override
        public Void apply(KToken k) {
            if (useNativeBooleanExp && inBooleanExp && k.sort().equals(Sorts.Bool())) {
                sb.append(k.s());
                return null;
            }
            if (mainModule.sortAttributesFor().contains(k.sort())) {
                String hook = mainModule.sortAttributesFor().apply(k.sort()).<String>getOptional("hook").orElse("");
                if (sortHooks.containsKey(hook)) {
                    sb.append(sortHooks.get(hook).apply(k.s()));
                    return null;
                }
            }
            sb.append("KToken (");
            apply(k.sort());
            sb.append(", ");
            sb.append(StringUtil.enquoteCString(k.s()));
            sb.append(")");
            return null;
        }

        @Override
        public Void apply(KVariable k) {
            if (rhs) {
                applyVarRhs(k, sb, vars);
            } else {
                applyVarLhs(k, sb, vars);
            }
            return null;
        }

        @Override
        public Void apply(KSequence k) {
            if (useNativeBooleanExp && k.items().size() == 1 && inBooleanExp) {
                apply(k.items().get(0));
                return null;
            }
            sb.append("(");
            if (!rhs) {
                for (int i = 0; i < k.items().size() - 1; i++) {
                    if (isList(k.items().get(i), false, rhs, vars)) {
                        throw KEMException.criticalError("Cannot compile KSequence with K variable not at tail.", k.items().get(i));
                    }
                }
            }
            apply(k.items(), false);
            sb.append(")");
            return null;
        }

        @Override
        public Void apply(InjectedKLabel k) {
            sb.append("InjectedKLabel (");
            apply(k.klabel());
            sb.append(")");
            return null;
        }

        private void apply(List<K> items, boolean klist) {
            for (int i = 0; i < items.size(); i++) {
                K item = items.get(i);
                apply(item);
                if (i != items.size() - 1) {
                    if (isList(item, klist, rhs, vars)) {
                        sb.append(" @ ");
                    } else {
                        sb.append(" :: ");
                    }
                } else {
                    if (!isList(item, klist, rhs, vars)) {
                        sb.append(" :: []");
                    }
                }
            }
            if (items.size() == 0)
                sb.append("[]");
        }

        private void apply(Sort sort) {
            encodeStringToIdentifier(sb, sort);
        }

        public void apply(KLabel klabel) {
            if (klabel instanceof KVariable) {
                apply((KVariable) klabel);
            } else {
                encodeStringToIdentifier(sb, klabel);
            }
        }
    }

    public static String getSortOfVar(KVariable k, VarInfo vars) {
        if (vars.listVars.containsKey(k)) {
            return vars.listVars.get(k).name();
        }
        return k.att().<String>getOptional(Attribute.SORT_KEY).orElse("K");
    }

    private boolean isLookupKLabel(KApply k) {
        return k.klabel().name().equals("#match") || k.klabel().name().equals("#mapChoice") || k.klabel().name().equals("#setChoice");
    }

    private boolean isList(K item, boolean klist, boolean rhs, VarInfo vars) {
        return !klist && ((item instanceof KVariable && getSortOfVar((KVariable)item, vars).equals("K")) || item instanceof KSequence
                || (item instanceof KApply && (functions.contains(((KApply) item).klabel()) || ((anywhereKLabels.contains(((KApply) item).klabel()) || ((KApply) item).klabel() instanceof KVariable) && rhs))))
                && !(!rhs && item instanceof KApply && collectionFor.containsKey(((KApply) item).klabel()));
    }

}
