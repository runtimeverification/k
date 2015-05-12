package org.kframework.backend.ocaml;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.java.kore.compile.ExpandMacros;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.kil.Attribute;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
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
import org.kframework.kore.compile.DeconstructIntegerLiterals;
import org.kframework.kore.compile.GenerateSortPredicateRules;
import org.kframework.kore.compile.LiftToKSequence;
import org.kframework.kore.compile.RewriteToTop;
import org.kframework.kore.compile.VisitKORE;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Function1;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
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

    public static final boolean fastCompilation = true;
    public static final Pattern identChar = Pattern.compile("[A-Za-z0-9_]");

    public static final String kType = "t = kitem list\n" +
            " and kitem = KApply of klabel * t list\n" +
            "           | KToken of sort * string\n" +
            "           | InjectedKLabel of klabel\n" +
            "           | Map of t m\n" +
            "           | List of t list\n" +
            "           | Set of s\n" +
            "           | Int of Z.t\n" +
            "           | String of string\n" +
            "           | Bool of bool\n" +
            "           | Bottom\n";

    public static final String prelude = "module type S =\n" +
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
            "    | (KApply(kl1, k1)), (KApply(kl2, k2)) -> let v = compare_klabel kl1 kl2 in if v = 0 then compare_klist k1 k2 else v\n" +
            "    | (KToken(s1, st1)), (KToken(s2, st2)) -> let v = compare_sort s1 s2 in if v = 0 then Pervasives.compare st1 st2 else v\n" +
            "    | (InjectedKLabel kl1), (InjectedKLabel kl2) -> compare_klabel kl1 kl2\n" +
            "    | (Map m1), (Map m2) -> (KMap.compare) compare m1 m2\n" +
            "    | (List l1), (List l2) -> compare_klist l1 l2\n" +
            "    | (Set s1), (Set s2) -> (KSet.compare) s1 s2\n" +
            "    | (Int i1), (Int i2) -> Z.compare i1 i2\n" +
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
            "    | String(_), _ -> -1\n" +
            "    | _, String(_) -> 1\n" +
            "    | Bool(_), _ -> -1\n" +
            "    | _, Bool(_) -> 1\n" +
            "  and compare_klist c1 c2 = match (c1, c2) with\n" +
            "    | [], [] -> 0\n" +
            "    | (hd1 :: tl1), (hd2 :: tl2) -> let v = compare hd1 hd2 in if v = 0 then compare_klist tl1 tl2 else v\n" +
            "    | (hd1 :: tl1), _ -> -1\n" +
            "    | _ -> 1\n" +
            "  and compare_klabel kl1 kl2 = (order_klabel kl2) - (order_klabel kl1)\n" +
            "  and compare_sort s1 s2 = (order_sort s2) - (order_sort s1)\n" +
            "end\n" +
            "\n" +
            "  module KMap = Map.Make(K)\n" +
            "  module KSet = Set.Make(K)\n" +
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
            "let freshCounter : Z.t ref = ref Z.zero\n" ;
    public static final String TRUE = "(Bool true)";
    public static final String BOOL = encodeStringToIdentifier(Sort("Bool"));
    public static final String STRING = encodeStringToIdentifier(Sort("String"));
    public static final String INT = encodeStringToIdentifier(Sort("Int"));

    public static final String midlude = "let eq k1 k2 = k1 = k2\n" +
            "let isTrue(c: k) : bool = match c with\n" +
            "| ([" + TRUE + "]) -> true\n" +
            "| _ -> false\n" +
            "let rec list_range (c: k list * int * int) : k list = match c with\n" +
            "| (_, 0, 0) -> []\n" +
            "| (head :: tail, 0, len) -> head :: list_range(tail, 0, len - 1)\n" +
            "| (_ :: tail, n, len) -> list_range(tail, n - 1, len)\n" +
            "| ([], _, _) -> raise(Failure \"list_range\")\n" +
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
            "| Bottom -> \"`#Bottom`(.KList)\"\n" +
            "| List(l) -> List.fold_left (fun s k -> \"`_List_`(`ListItem`(\" ^ print_k(k) ^ \"),\" ^ s ^ \")\") \"`.List`(.KList)\" l\n" +
            "| Set(s) -> KSet.fold (fun k s -> \"`_Set_`(`SetItem`(\" ^ print_k(k) ^ \"), \" ^ s ^ \")\") s \"`.Set`(.KList)\"\n" +
            "| Map(m) -> KMap.fold (fun k v s -> \"`_Map_`(`_|->_`(\" ^ print_k(k) ^ \", \" ^ print_k(v) ^ \"), \" ^ s ^ \")\") m \"`.Map`(.KList)\"\n" +
            "let print_set f s = print_string (print_kitem(Set s))\n" +
            "let print_map f m = print_string (print_kitem(Map m))\n";

    public static final String postlude = "let run c n=\n" +
            "  try let rec go c n = if n = 0 then c else go (step c) (n - 1)\n" +
            "      in go c n\n" +
            "  with Stuck c' -> c'\n";

    public static final ImmutableMap<String, String> hooks;
    public static final ImmutableMap<String, Function<String, String>> sortHooks;
    public static final ImmutableMap<String, String> predicateRules;

    static {
        ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
        builder.put("Map:_|->_", "k1 :: k2 :: [] -> [Map (KMap.singleton k1 k2)]");
        builder.put("Map:.Map", "[] -> [Map KMap.empty]");
        builder.put("Map:__", "([Map k1]) :: ([Map k2]) :: [] -> [Map (KMap.merge (fun k a b -> match a, b with None, None -> None | None, Some v | Some v, None -> Some v | Some v1, Some v2 when v1 = v2 -> Some v1) k1 k2)]");
        builder.put("Map:lookup", "[Map k1] :: k2 :: [] -> (try KMap.find k2 k1 with Not_found -> [Bottom])");
        builder.put("Map:update", "[Map k1] :: k :: v :: [] -> [Map (KMap.add k v k1)]");
        builder.put("Map:remove", "[Map k1] :: k2 :: [] -> [Map (KMap.remove k2 k1)]");
        builder.put("Map:keys", "[Map k1] :: [] -> [Set (KMap.fold (fun k v -> KSet.add k) k1 KSet.empty)]");
        builder.put("Map:values", "[Map k1] :: [] -> [Set (KMap.fold (fun key -> KSet.add) k1 KSet.empty)]");
        builder.put("Map:choice", "[Map k1] :: [] -> match KMap.choose k1 with (k, _) -> k");
        builder.put("Map:updateAll", "([Map k1]) :: ([Map k2]) :: [] -> [Map (KMap.merge (fun k a b -> match a, b with None, None -> None | None, Some v | Some v, None | Some _, Some v -> Some v) k1 k2)]");
        builder.put("Set:in", "k1 :: [Set k2] :: [] -> [Bool (KSet.mem k1 k2)]");
        builder.put("Set:.Set", "[] -> [Set KSet.empty]");
        builder.put("Set:SetItem", "k :: [] -> [Set (KSet.singleton k)]");
        builder.put("Set:__", "[Set s1] :: [Set s2] :: [] -> [Set (KSet.union s1 s2)]");
        builder.put("Set:difference", "[Set k1] :: [Set k2] :: [] -> [Set (KSet.diff k1 k2)]");
        builder.put("Set:inclusion", "[Set k1] :: [Set k2] :: [] -> [Bool (KSet.subset k1 k2)]");
        builder.put("Set:intersection", "[Set k1] :: [Set k2] :: [] -> [Set (KSet.inter k1 k2)]");
        builder.put("Set:choice", "[Set k1] :: [] -> KSet.choose k1");
        builder.put("List:.List", "[] -> [List []]");
        builder.put("List:ListItem", "k :: [] -> [List [k]]");
        builder.put("List:__", "[List l1] :: [List l2] :: [] -> [List (l1 @ l2)]");
        builder.put("List:in", "k1 :: [List k2] :: [] -> [Bool (List.mem k1 k2)]");
        builder.put("List:get", "[List l1] :: [Int i] :: [] -> let i = Z.to_int i in (try if i >= 0 then List.nth l1 i else List.nth l1 ((List.length l1) + i) with Failure \"nth\" -> [Bottom])");
        builder.put("List:range", "[List l1] :: [Int i1] :: [Int i2] :: [] -> (try [List (list_range (l1, (Z.to_int i1), (List.length(l1) - (Z.to_int i2) - (Z.to_int i1))))] with Failure \"list_range\" -> [Bottom])");
        builder.put("Collection:size", "[List l] :: [] -> [Int (Z.of_int (List.length l))] " +
                "| [Map m] :: [] -> [Int (Z.of_int (KMap.cardinal m))] " +
                "| [Set s] :: [] -> [Int (Z.of_int (KSet.cardinal s))]");
        builder.put("MetaK:#sort", "[KToken (sort, s)] :: [] -> [String (print_sort(sort))] " +
                "| [Int _] :: [] -> [String \"Int\"] " +
                "| [String _] :: [] -> [String \"String\"] " +
                "| [Bool _] :: [] -> [String \"Bool\"] " +
                "| [Map _] :: [] -> [String \"Map\"] " +
                "| [List _] :: [] -> [String \"List\"] " +
                "| [Set _] :: [] -> [String \"Set\"] " +
                "| _ -> [String \"\"]");
        builder.put("#K-EQUAL:_==K_", "k1 :: k2 :: [] -> [Bool (eq k1 k2)]");
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
        builder.put("#STRING:substrString", "[String s] :: [Int i1] :: [Int i2] :: [] -> [String (String.sub s (Z.to_int i1) (Z.to_int (Z.add i1 i2)))]");
        builder.put("#STRING:ordChar", "[String s] :: [] -> [Int (Z.of_int (Char.code (String.get s 0)))]");
        builder.put("#INT:_%Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.rem a b)]");
        builder.put("#INT:_+Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.add a b)]");
        builder.put("#INT:_<=Int_", "[Int a] :: [Int b] :: [] -> [Bool (Z.leq a b)]");
        builder.put("#INT:_&Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.logand a b)]");
        builder.put("#INT:_*Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.mul a b)]");
        builder.put("#INT:_-Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.sub a b)]");
        builder.put("#INT:_/Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.div a b)]");
        builder.put("#INT:_<<Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.shift_left a (Z.to_int b))]");
        builder.put("#INT:_<Int_", "[Int a] :: [Int b] :: [] -> [Bool (Z.lt a b)]");
        builder.put("#INT:_>=Int_", "[Int a] :: [Int b] :: [] -> [Bool (Z.geq a b)]");
        builder.put("#INT:_>>Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.shift_right a (Z.to_int b))]");
        builder.put("#INT:_>Int_", "[Int a] :: [Int b] :: [] -> [Bool (Z.gt a b)]");
        builder.put("#INT:_^Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.pow a (Z.to_int b))]");
        builder.put("#INT:_xorInt_", "[Int a] :: [Int b] :: [] -> [Int (Z.logxor a b)]");
        builder.put("#INT:_|Int_", "[Int a] :: [Int b] :: [] -> [Int (Z.logor a b)]");
        builder.put("#INT:absInt", "[Int a] :: [] -> [Int (Z.abs a)]");
        builder.put("#INT:maxInt", "[Int a] :: [Int b] :: [] -> [Int (Z.max a b)]");
        builder.put("#INT:minInt", "[Int a] :: [Int b] :: [] -> [Int (Z.min a b)]");
        builder.put("#CONVERSION:int2string", "[Int i] :: [] -> [String (Z.to_string i)]");
        builder.put("#CONVERSION:string2int", "[String s] :: [] -> [Int (Z.of_string s)]");
        builder.put("#CONVERSION:string2base", "[String s] :: [Int i] :: [] -> [Int (Z.of_string_base (Z.to_int i) s)]");
        builder.put("#FRESH:fresh", "[String sort] :: [] -> let res = freshFunction sort !freshCounter in freshCounter := Z.add !freshCounter Z.one; res");
        hooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, Function<String, String>> builder = ImmutableMap.builder();
        builder.put("#BOOL", s -> "(Bool " + s + ")");
        builder.put("#INT", s -> "(Int (Z.of_string \"" + s + "\"))");
        builder.put("#STRING", s -> "(String " + StringUtil.enquoteCString(StringUtil.unquoteKString(StringUtil.unquoteKString("\"" + s + "\""))) + ")");
        sortHooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
        builder.put("isK", "k1 :: [] -> [Bool true]");
        builder.put("isKItem", "[k1] :: [] -> [Bool true]");
        builder.put("isInt", "[Int _] :: [] -> [Bool true]");
        builder.put("isString", "[String _] :: [] -> [Bool true]");
        builder.put("isBool", "[Bool _] :: [] -> [Bool true]");
        builder.put("isMap", "[Map _] :: [] -> [Bool true]");
        builder.put("isSet", "[Set _] :: [] -> [Bool true]");
        builder.put("isList", "[List _] :: [] -> [Bool true]");
        predicateRules = builder.build();
    }


    private Module mainModule;

    public String convert(CompiledDefinition def) {
        Function1<Module, Module> generatePredicates = func(new GenerateSortPredicateRules(def.kompiledDefinition)::gen);
        ModuleTransformer convertLookups = ModuleTransformer.fromSentenceTransformer(new ConvertDataStructureToLookup(def.executionModule())::convert, "convert data structures to lookups");
        ModuleTransformer liftToKSequence = ModuleTransformer.fromSentenceTransformer(new LiftToKSequence()::convert, "lift K into KSequence");
        this.expandMacros = new ExpandMacros(def.executionModule(), kem, files, globalOptions, kompileOptions);
        ModuleTransformer expandMacros = ModuleTransformer.fromSentenceTransformer(this.expandMacros::expand, "expand macro rules");
        ModuleTransformer deconstructInts = ModuleTransformer.fromSentenceTransformer(new DeconstructIntegerLiterals()::convert, "remove matches on integer literals in left hand side");
        Function1<Module, Module> pipeline = deconstructInts
                .andThen(convertLookups)
                .andThen(expandMacros)
                .andThen(generatePredicates)
                .andThen(liftToKSequence);
        mainModule = pipeline.apply(def.executionModule());
        return convert();
    }

    Set<KLabel> functions;
    Set<KLabel> anywhereKLabels;

    public String convert(K k, int depth) {
        StringBuilder sb = new StringBuilder();
        sb.append("open Def\nopen K\n");
        sb.append("let _ = print_string(print_k(try(run(");
        convert(sb, true, HashMultimap.create(), false).apply(new LiftToKSequence().convert(expandMacros.expand(k)));
        sb.append(") (").append(depth).append(")) with Stuck c' -> c'))");
        return sb.toString();
    }

    private String convert() {
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
        }
        sb.append("let order_sort(s: sort) = match s with \n");
        int i = 0;
        for (Sort s : iterable(mainModule.definedSorts())) {
            sb.append("|");
            encodeStringToIdentifier(sb, s);
            sb.append(" -> ").append(i++).append("\n");
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
        i = 0;
        sb.append("let order_klabel(l: klabel) = match l with \n");
        for (KLabel label : iterable(mainModule.definedKLabels())) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ").append(i++).append("\n");
        }
        sb.append(prelude);
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
        sb.append(midlude);
        SetMultimap<KLabel, Rule> functionRules = HashMultimap.create();
        SetMultimap<KLabel, Rule> anywhereRules = HashMultimap.create();
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
            sb.append(" (c: k list) (guards: Guard.t) : k = let lbl = \n");
            encodeStringToIdentifier(sb, functionLabel);
            sb.append(" in match c with \n");
            String hook = mainModule.attributesFor().apply(functionLabel).<String>getOptional(Attribute.HOOK_KEY).orElse("");
            if (hooks.containsKey(hook)) {
                sb.append("| ");
                sb.append(hooks.get(hook));
                sb.append("\n");
                if (fastCompilation) {
                    sb.append("| _ -> match c with \n");
                }
            } else if (!hook.isEmpty()) {
                kem.registerCompilerWarning("missing entry for hook " + hook);
            }
            if (predicateRules.containsKey(functionLabel.name())) {
                sb.append("| ");
                sb.append(predicateRules.get(functionLabel.name()));
                sb.append("\n");
                if (fastCompilation) {
                    sb.append("| _ -> match c with \n");
                }
            }

            i = 0;
            for (Rule r : functionRules.get(functionLabel).stream().sorted(this::sortFunctionRules).collect(Collectors.toList())) {
                convert(r, sb, RuleType.FUNCTION, i++, functionName);
                if (fastCompilation) {
                    sb.append("| _ -> match c with \n");
                }
            }
            sb.append("| _ -> raise (Stuck [KApply(lbl, c)])\n");
            conn = "and ";
        }
        for (KLabel functionLabel : anywhereKLabels) {
            sb.append(conn);
            String functionName = encodeStringToFunction(sb, functionLabel.name());
            sb.append(" (c: k list) (guards: Guard.t) : k = let lbl = \n");
            encodeStringToIdentifier(sb, functionLabel);
            sb.append(" in match c with \n");
            i = 0;
            for (Rule r : anywhereRules.get(functionLabel)) {
                convert(r, sb, RuleType.ANYWHERE, i++, functionName);
                if (fastCompilation) {
                    sb.append("| _ -> match c with \n");
                }
            }
            sb.append("| _ -> [KApply(lbl, c)]\n");
            conn = "and ";
        }

        sb.append("and freshFunction (sort: string) (counter: Z.t) : k = match sort with \n");
        for (Sort sort : iterable(mainModule.freshFunctionFor().keys())) {
            sb.append("| \"").append(sort.name()).append("\" -> (");
            KLabel freshFunction = mainModule.freshFunctionFor().apply(sort);
            encodeStringToFunction(sb, freshFunction.name());
            sb.append(" ([Int counter] :: []) Guard.empty)\n");
        }
        sb.append("and eval (c: kitem) : k = match c with KApply(lbl, kl) -> match lbl with \n");
        for (KLabel label : Sets.union(functions, anywhereKLabels)) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            encodeStringToFunction(sb, label.name());
            sb.append(" kl Guard.empty\n");
        }
        sb.append("| _ -> [c]");
        boolean hasLookups = false;
        Map<Boolean, List<Rule>> sortedRules = stream(mainModule.rules())
                .filter(r -> !functionRules.values().contains(r) && !r.att().contains(Attribute.MACRO_KEY))
                .collect(Collectors.groupingBy(this::hasLookups));
        sb.append("let rec lookups_step (c: k) (guards: Guard.t) : k = match c with \n");
        i = 0;
        for (Rule r : sortedRules.get(true)) {
            convert(r, sb, RuleType.REGULAR, i++, "lookups_step");
            if (fastCompilation) {
                sb.append("| _ -> match c with \n");
            }
        }
        sb.append("| _ -> raise (Stuck c)\n");
        sb.append("let step (c: k) : k = match c with \n");
        for (Rule r : sortedRules.get(false)) {
            convert(r, sb, RuleType.REGULAR, i++, "step");
            if (fastCompilation) {
                sb.append("| _ -> match c with \n");
            }
        }
        sb.append("| _ -> lookups_step c Guard.empty\n");
        sb.append(postlude);
        return sb.toString();
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
            sb.append("Sort(\"").append(name.name().replace("\"", "\\\"")).append("\")");
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
        FUNCTION, ANYWHERE, REGULAR
    }

    private void convert(Rule r, StringBuilder sb, RuleType type, int ruleNum, String functionName) {
        try {
            sb.append("(* rule ");
            sb.append(ToKast.apply(r.body()));
            sb.append(" requires ");
            sb.append(ToKast.apply(r.requires()));
            sb.append(" ensures ");
            sb.append(ToKast.apply(r.ensures()));
            sb.append(" ");
            sb.append(r.att().toString());
            sb.append("*)\n");
            sb.append("| ");
            K left = RewriteToTop.toLeft(r.body());
            K right = RewriteToTop.toRight(r.body());
            K requires = r.requires();
            SetMultimap<KVariable, String> vars = HashMultimap.create();
            Visitor visitor = convert(sb, false, vars, false);
            if (type == RuleType.ANYWHERE || type == RuleType.FUNCTION) {
                KApply kapp = (KApply) ((KSequence) left).items().get(0);
                visitor.apply(kapp.klist().items(), true);
            } else {
                visitor.apply(left);
            }
            String result = convert(vars);
            if (hasLookups(r)) {
                sb.append(" when not (Guard.mem (GuardElt.Guard ").append(ruleNum).append(") guards)");
            }
            String suffix = "";
            if (!requires.equals(KSequence(BooleanUtils.TRUE)) || !result.equals("true")) {
                suffix = convertLookups(sb, requires, vars, functionName, ruleNum);
                result = convert(vars);
                sb.append(" when ");
                convert(sb, true, vars, true).apply(requires);
                sb.append(" && (");
                sb.append(result);
                sb.append(")");
            }
            sb.append(" -> ");
            if (type == RuleType.ANYWHERE) {
                sb.append("(match ");
            }
            convert(sb, true, vars, false).apply(right);
            if (type == RuleType.ANYWHERE) {
                sb.append(" with [item] -> eval item)");
            }
            sb.append(suffix);
            sb.append("\n");
        } catch (KEMException e) {
            e.exception.addTraceFrame("while compiling rule at " + r.att().getOptional(Source.class).map(Object::toString).orElse("<none>") + ":" + r.att().getOptional(Location.class).map(Object::toString).orElse("<none>"));
            throw e;
        }
    }

    private static class Holder { int i; }

    private String convertLookups(StringBuilder sb, K requires, SetMultimap<KVariable, String> vars, String functionName, int ruleNum) {
        Deque<String> suffix = new ArrayDeque<>();
        Holder h = new Holder();
        h.i = 0;
        new VisitKORE() {
            @Override
            public Void apply(KApply k) {
                if (k.klabel().name().equals("#match")) {
                    if (k.klist().items().size() != 2) {
                        throw KEMException.internalError("Unexpected arity of lookup: " + k.klist().size(), k);
                    }
                    sb.append(" -> (match ");
                    convert(sb, true, vars, false).apply(k.klist().items().get(1));
                    sb.append(" with \n");
                    String reapply = "(" + functionName + " c (Guard.add (GuardElt.Guard " + ruleNum + ") guards))";
                    sb.append("| [Bottom] -> ").append(reapply).append("\n| ");
                    convert(sb, false, vars, false).apply(k.klist().items().get(0));
                    suffix.add("| _ -> " + reapply + ")");
                    h.i++;
                } else if (k.klabel().name().equals("#setChoice")) {
                    if (k.klist().items().size() != 2) {
                        throw KEMException.internalError("Unexpected arity of choice: " + k.klist().size(), k);
                    }
                    sb.append(" -> (match ");
                    convert(sb, true, vars, false).apply(k.klist().items().get(1));
                    sb.append(" with \n");
                    sb.append("| [Set s] -> let choice = (KSet.fold (fun e result -> if result = [Bottom] then (match e with ");
                    convert(sb, false, vars, false).apply(k.klist().items().get(0));
                    suffix.add("| _ -> (" + functionName + " c (Guard.add (GuardElt.Guard " + ruleNum + ") guards)))");
                    suffix.add("| _ -> [Bottom]) else result) s [Bottom]) in if choice = [Bottom] then (" + functionName + " c (Guard.add (GuardElt.Guard " + ruleNum + ") guards)) else choice");
                    h.i++;
                } else if (k.klabel().name().equals("#mapChoice")) {
                    if (k.klist().items().size() != 2) {
                        throw KEMException.internalError("Unexpected arity of choice: " + k.klist().size(), k);
                    }
                    sb.append(" -> (match ");
                    convert(sb, true, vars, false).apply(k.klist().items().get(1));
                    sb.append(" with \n");
                    sb.append("| [Map m] -> let choice = (KMap.fold (fun k v result -> if result = [Bottom] then (match k with ");
                    convert(sb, false, vars, false).apply(k.klist().items().get(0));
                    suffix.add("| _ -> (" + functionName + " c (Guard.add (GuardElt.Guard " + ruleNum + ") guards)))");
                    suffix.add("| _ -> [Bottom]) else result) m [Bottom]) in if choice = [Bottom] then (" + functionName + " c (Guard.add (GuardElt.Guard " + ruleNum + ") guards)) else choice");
                    h.i++;
                }
                return super.apply(k);
            }
        }.apply(requires);
        StringBuilder sb2 = new StringBuilder();
        while (!suffix.isEmpty()) {
            sb2.append(suffix.pollLast());
        }
        return sb2.toString();
    }

    private static String convert(SetMultimap<KVariable, String> vars) {
        StringBuilder sb = new StringBuilder();
        for (Collection<String> nonLinearVars : vars.asMap().values()) {
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

    private void applyVarRhs(KVariable v, StringBuilder sb, SetMultimap<KVariable, String> vars) {
        sb.append(vars.get(v).iterator().next());
    }

    private void applyVarLhs(KVariable k, StringBuilder sb, SetMultimap<KVariable, String> vars) {
        String varName = encodeStringToVariable(k.name());
        vars.put(k, varName);
        Sort s = Sort(k.att().<String>getOptional(Attribute.SORT_KEY).orElse(""));
        if (mainModule.sortAttributesFor().contains(s)) {
            String hook = mainModule.sortAttributesFor().apply(s).<String>getOptional("hook").orElse("");
            if (sortHooks.containsKey(hook)) {
                sb.append("(");
                sb.append(s.name()).append(" _");
                sb.append(" as ").append(varName).append(")");
                return;
            }
        }
        sb.append(varName);
    }

    private Visitor convert(StringBuilder sb, boolean rhs, SetMultimap<KVariable, String> vars, boolean useNativeBooleanExp) {
        return new Visitor(sb, rhs, vars, useNativeBooleanExp);
    }

    private class Visitor extends VisitKORE {
        private final StringBuilder sb;
        private final boolean rhs;
        private final SetMultimap<KVariable, String> vars;
        private final boolean useNativeBooleanExp;

        public Visitor(StringBuilder sb, boolean rhs, SetMultimap<KVariable, String> vars, boolean useNativeBooleanExp) {
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
                sb.append("eval (");
                applyKLabel(k);
                sb.append(")");
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
            } else if (mainModule.collectionFor().contains(k.klabel()) && !rhs) {
                applyKLabel(k);
                sb.append(" :: []");
            } else {
                if (mainModule.attributesFor().apply(k.klabel()).contains(Attribute.PREDICATE_KEY)) {
                    Sort s = Sort(mainModule.attributesFor().apply(k.klabel()).<String>get(Attribute.PREDICATE_KEY).get());
                    if (mainModule.sortAttributesFor().contains(s)) {
                        String hook2 = mainModule.sortAttributesFor().apply(s).<String>getOptional("hook").orElse("");
                        if (sortHooks.containsKey(hook2)) {
                            if (k.klist().items().size() == 1) {
                                KSequence item = (KSequence) k.klist().items().get(0);
                                if (item.items().size() == 1 &&
                                        vars.containsKey(item.items().get(0))) {
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
                sb.append(") Guard.empty)");
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
                    if (isList(k.items().get(i), false)) {
                        throw KEMException.criticalError("Cannot compile KSequence with K variable not at tail.", k.items().get(i));
                    }
                }
            }
            apply(k.items(), false);
            sb.append(")");
            return null;
        }

        public String getSortOfVar(K k) {
            return k.att().<String>getOptional(Attribute.SORT_KEY).orElse("K");
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
                    if (isList(item, klist)) {
                        sb.append(" @ ");
                    } else {
                        sb.append(" :: ");
                    }
                } else {
                    if (!isList(item, klist)) {
                        sb.append(" :: []");
                    }
                }
            }
            if (items.size() == 0)
                sb.append("[]");
        }

        private boolean isList(K item, boolean klist) {
            return !klist && ((item instanceof KVariable && getSortOfVar(item).equals("K")) || item instanceof KSequence
                    || (item instanceof KApply && (functions.contains(((KApply) item).klabel()) || ((anywhereKLabels.contains(((KApply) item).klabel()) || ((KApply) item).klabel() instanceof KVariable) && rhs))));
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

    private boolean isLookupKLabel(KApply k) {
        return k.klabel().name().equals("#match") || k.klabel().name().equals("#mapChoice") || k.klabel().name().equals("#setChoice");
    }
}
