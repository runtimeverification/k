// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.BiMap;
import com.google.common.collect.ComparisonChain;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
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
import org.kframework.definition.NonTerminal;
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
import scala.Tuple2;
import scala.Tuple3;

import java.io.Serializable;
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
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;
import static scala.compat.java8.JFunction.*;

public class DefinitionToOcaml implements Serializable {

    private transient final KExceptionManager kem;
    private transient final FileUtil files;
    private transient final GlobalOptions globalOptions;
    private transient final KompileOptions kompileOptions;
    private transient ExpandMacros expandMacros;

    public DefinitionToOcaml(KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions) {
        this.kem = kem;
        this.files = files;
        this.globalOptions = globalOptions;
        this.kompileOptions = kompileOptions;
    }
    public static final boolean ocamlopt = true;
    public static final boolean fastCompilation = false;
    public static final Pattern identChar = Pattern.compile("[A-Za-z0-9_]");

    public static final String BOOL = encodeStringToIdentifier(Sort("Bool"));
    public static final String STRING = encodeStringToIdentifier(Sort("String"));
    public static final String INT = encodeStringToIdentifier(Sort("Int"));
    public static final String FLOAT = encodeStringToIdentifier(Sort("Float"));
    public static final String SET = encodeStringToIdentifier(Sort("Set"));
    public static final String SET_CONCAT = encodeStringToIdentifier(KLabel("_Set_"));
    public static final String LIST = encodeStringToIdentifier(Sort("List"));
    public static final String LIST_CONCAT = encodeStringToIdentifier(KLabel("_List_"));

    public static final String postlude = "let run c n=\n" +
            "  try let rec go c n = if n = 0 then c else go (step c) (n - 1)\n" +
            "      in go c n\n" +
            "  with Stuck c' -> c'\n";

    public static final ImmutableSet<String> hookNamespaces;
    public static final ImmutableMap<String, Function<String, String>> sortHooks;
    public static final ImmutableMap<String, Function<Sort, String>> sortVarHooks;
    public static final ImmutableMap<String, Function<Sort, String>> predicateRules;

    static {
        ImmutableSet.Builder<String> builder = ImmutableSet.builder();
        builder.add("BOOL").add("FLOAT").add("INT").add("IO").add("K").add("KEQUAL").add("KREFLECTION").add("LIST");
        builder.add("MAP").add("MINT").add("SET").add("STRING");
        hookNamespaces = builder.build();
    }

    static {
        ImmutableMap.Builder<String, Function<String, String>> builder = ImmutableMap.builder();
        builder.put("BOOL.Bool", s -> "(Bool " + s + ")");
        builder.put("INT.Int", s -> "(Lazy.force " + encodeStringToIntConst(s) + ")");
        builder.put("FLOAT.Float", s -> {
            Pair<BigFloat, Integer> f = FloatBuiltin.parseKFloat(s);
            return "(round_to_range(Float ((FR.from_string_prec_base " + f.getLeft().precision() + " GMP_RNDN 10 \"" + f.getLeft().toString() + "\"), " + f.getRight() + ", " + f.getLeft().precision() + ")))";
        });
        builder.put("STRING.String", s -> "(String " + enquoteString(StringUtil.unquoteKString(StringUtil.unquoteKString("\"" + s + "\""))) + ")");
        sortHooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, Function<Sort, String>> builder = ImmutableMap.builder();
        builder.put("BOOL.Bool", s -> "Bool _");
        builder.put("INT.Int", s -> "Int _");
        builder.put("FLOAT.Float", s -> "Float _");
        builder.put("STRING.String", s -> "String _");
        builder.put("LIST.List", s -> "List (" + encodeStringToIdentifier(s) + ",_,_)");
        builder.put("MAP.Map", s -> "Map (" + encodeStringToIdentifier(s) + ",_,_)");
        builder.put("SET.Set", s -> "Set (" + encodeStringToIdentifier(s) + ",_,_)");
        sortVarHooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, Function<Sort, String>> builder = ImmutableMap.builder();
        builder.put("K.K", s -> "k1 -> [Bool true]");
        builder.put("K.KItem", s -> "[k1] -> [Bool true]");
        builder.put("INT.Int", s -> "[Int _] -> [Bool true]");
        builder.put("FLOAT.Float", s -> "[Float _] -> [Bool true]");
        builder.put("STRING.String", s -> "[String _] -> [Bool true]");
        builder.put("BOOL.Bool", s -> "[Bool _] -> [Bool true]");
        builder.put("MAP.Map", s -> "[Map (s,_,_)] when (s = " + encodeStringToIdentifier(s) + ") -> [Bool true]");
        builder.put("SET.Set", s -> "[Set (s,_,_)] when (s = " + encodeStringToIdentifier(s) + ") -> [Bool true]");
        builder.put("LIST.List", s -> "[List (s,_,_)] when (s = " + encodeStringToIdentifier(s) + ") -> [Bool true]");
        predicateRules = builder.build();
    }


    private Module mainModule;
    private Map<KLabel, KLabel> collectionFor;

    public void initialize(DefinitionToOcaml serialized, CompiledDefinition def) {
        mainModule = serialized.mainModule;
        collectionFor = serialized.collectionFor;
        functions = serialized.functions;
        anywhereKLabels = serialized.anywhereKLabels;
        expandMacros = new ExpandMacros(def.executionModule(), kem, files, globalOptions, kompileOptions);
        klabels = serialized.klabels;
    }

    public void initialize(CompiledDefinition def) {
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

    public static String enquoteString(String value) {
        char delimiter = '"';
        final int length = value.length();
        StringBuilder result = new StringBuilder();
        result.append(delimiter);
        for (int offset = 0, codepoint; offset < length; offset += Character.charCount(codepoint)) {
            codepoint = value.codePointAt(offset);
            if (codepoint > 0xFF) {
                throw KEMException.compilerError("Unsupported: unicode characters in strings in Ocaml backend.");
            } else if (codepoint == delimiter) {
                result.append("\\").append(delimiter);
            } else if (codepoint == '\\') {
                result.append("\\\\");
            } else if (codepoint == '\n') {
                result.append("\\n");
            } else if (codepoint == '\t') {
                result.append("\\t");
            } else if (codepoint == '\r') {
                result.append("\\r");
            } else if (codepoint == '\b') {
                result.append("\\b");
            } else if (codepoint >= 32 && codepoint < 127) {
                result.append((char)codepoint);
            } else if (codepoint <= 0xff) {
                result.append("\\");
                result.append(String.format("%03d", codepoint));
            }
        }
        result.append(delimiter);
        return result.toString();
    }

    public String execute(K k, int depth, String file) {
        StringBuilder sb = new StringBuilder();
        sb.append("open Prelude\nopen Constants\nopen Constants.K\nopen Gmp\nopen Def\n");
        sb.append("let _ = let config = [Bottom] in let out = open_out ").append(enquoteString(file)).append(" in output_string out (print_k(try(run(");
        convert(sb, true, new VarInfo(), false, false).apply(new LiftToKSequence().lift(expandMacros.expand(k)));
        sb.append(") (").append(depth).append(")) with Stuck c' -> c'))");
        return sb.toString();
    }

    public String match(K k, Rule r, String file) {
        StringBuilder sb = new StringBuilder();
        sb.append("open Prelude\nopen Constants\nopen Constants.K\nopen Gmp\nopen Def\n");
        sb.append("let try_match (c: k) : k Subst.t = let config = c in match c with \n");
        convertFunction(Collections.singletonList(convert(r)), sb, "try_match", RuleType.PATTERN);
        sb.append("| _ -> raise(Stuck c)\n");
        sb.append("let _ = let config = [Bottom] in let out = open_out ").append(enquoteString(file)).append("in (try print_subst out (try_match(");
        convert(sb, true, new VarInfo(), false, false).apply(new LiftToKSequence().lift(expandMacros.expand(k)));
        sb.append("\n)) with Stuck c -> output_string out \"0\\n\")");
        return sb.toString();
    }

    public String executeAndMatch(K k, int depth, Rule r, String file, String substFile) {
        StringBuilder sb = new StringBuilder();
        sb.append("open Prelude\nopen Constants\nopen Constants.K\nopen Gmp\nopen Def\n");
        sb.append("let try_match (c: k) : k Subst.t = let config = c in match c with \n");
        convertFunction(Collections.singletonList(convert(r)), sb, "try_match", RuleType.PATTERN);
        sb.append("| _ -> raise(Stuck c)\n");
        sb.append("let _ = let config = [Bottom] in let out = open_out ").append(enquoteString(file)).append(" and subst = open_out ").append(enquoteString(substFile)).append(" in (try print_subst subst (try_match(let res = run(");
        convert(sb, true, new VarInfo(), false, false).apply(new LiftToKSequence().lift(expandMacros.expand(k)));
        sb.append("\n) (").append(depth).append(") in output_string out (print_k(res)); res)) with Stuck c -> output_string out (print_k(c)); output_string subst \"0\\n\")");
        return sb.toString();
    }

    public String constants() {
        StringBuilder sb = new StringBuilder();
        sb.append("open Gmp\n");
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
            sb.append(enquoteString(s.name()));
            sb.append("\n");
        }
        if (fastCompilation) {
            sb.append("| Sort s -> raise (Invalid_argument s)\n");
        }
        sb.append("let print_klabel(c: klabel) : string = match c with \n");
        for (KLabel label : iterable(mainModule.definedKLabels())) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            sb.append(enquoteString(ToKast.apply(label)));
            sb.append("\n");
        }
        if (fastCompilation) {
            sb.append("| KLabel s -> raise (Invalid_argument s)\n");
        }
        sb.append("let collection_for (c: klabel) : klabel = match c with \n");
        for (Map.Entry<KLabel, KLabel> entry : collectionFor.entrySet()) {
            sb.append("|");
            encodeStringToIdentifier(sb, entry.getKey());
            sb.append(" -> ");
            encodeStringToIdentifier(sb, entry.getValue());
            sb.append("\n");
        }
        sb.append("let unit_for (c: klabel) : klabel = match c with \n");
        for (KLabel label : collectionFor.values().stream().collect(Collectors.toSet())) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            encodeStringToIdentifier(sb, KLabel(mainModule.attributesFor().apply(label).<String>get(Attribute.UNIT_KEY).get()));
            sb.append("\n");
        }
        sb.append("let el_for (c: klabel) : klabel = match c with \n");
        for (KLabel label : collectionFor.values().stream().collect(Collectors.toSet())) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            encodeStringToIdentifier(sb, KLabel(mainModule.attributesFor().apply(label).<String>get("element").get()));
            sb.append("\n");
        }
        sb.append("let boolSort = ").append(BOOL);
        sb.append("\n and stringSort = ").append(STRING);
        sb.append("\n and intSort = ").append(INT);
        sb.append("\n and floatSort = ").append(FLOAT);
        sb.append("\n and setSort = ").append(SET);
        sb.append("\n and setConcatLabel = ").append(SET_CONCAT);
        sb.append("\n and listSort = ").append(LIST);
        sb.append("\n and listConcatLabel = ").append(LIST_CONCAT);
        sb.append("\n\nmodule type S =\n");
        sb.append("sig\n");
        sb.append("  type m\n");
        sb.append("  type s\n");
        sb.append("  type t = kitem list\n");
        List<Tuple2<KLabel, Long>> mostUsedLabels = printKType(sb);
        sb.append("  val compare : t -> t -> int\n" +
                "  val compare_kitem : kitem -> kitem -> int\n" +
                "  val compare_klist : t list -> t list -> int\n" +
                "end\n");
        sb.append("module rec K : (S with type m = K.t Map.Make(K).t and type s = Set.Make(K).t)  =\n" +
                "struct\n" +
                "  module KMap = Map.Make(K)\n" +
                "  module KSet = Set.Make(K)\n" +
                "  type m = K.t KMap.t\n" +
                "  and s = KSet.t\n" +
                "  and t = kitem list\n");
        printKType(sb);
        sb.append("  let rec compare c1 c2 = if c1 == c2 then 0 else match (c1, c2) with\n" +
                "    | [], [] -> 0\n" +
                "    | (hd1 :: tl1), (hd2 :: tl2) -> let v = compare_kitem hd1 hd2 in if v = 0 then compare tl1 tl2 else v\n" +
                "    | (hd1 :: tl1), _ -> -1\n" +
                "    | _ -> 1\n" +
                "  and compare_kitem c1 c2 = match (c1, c2) with\n");
        for(long arity : leftoverArities) {
            sb.append("    | KApply").append(arity).append("(lbl1");
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i).append("_1");
            }
            sb.append("),KApply").append(arity).append("(lbl2");
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i).append("_2");
            }
            if (arity > 0) {
                sb.append(") -> (let v = Pervasives.compare lbl1 lbl2 in if v = 0 then ");
                int i;
                for (i = 0; i < arity - 1; i++) {
                    sb.append("(let v = compare k").append(i).append("_1 k").append(i).append("_2 in if v = 0 then ");
                }
                sb.append("compare k").append(i).append("_1 k").append(i).append("_2\n");
                for (i = 0; i < arity; i++) {
                    sb.append(" else v)\n");
                }
            } else {
                sb.append(") -> Pervasives.compare lbl1 lbl2\n");
            }
        }
        sb.append("    | (KToken(s1, st1)), (KToken(s2, st2)) -> let v = Pervasives.compare s1 s2 in if v = 0 then Pervasives.compare st1 st2 else v\n" +
                "    | (InjectedKLabel kl1), (InjectedKLabel kl2) -> Pervasives.compare kl1 kl2\n" +
                "    | (Map (_,k1,m1)), (Map (_,k2,m2)) -> let v = Pervasives.compare k1 k2 in if v = 0 then (KMap.compare) compare m1 m2 else v\n" +
                "    | (List (_,k1,l1)), (List (_,k2,l2)) -> let v = Pervasives.compare k1 k2 in if v = 0 then compare_klist l1 l2 else v\n" +
                "    | (Set (_,k1,s1)), (Set (_,k2,s2)) -> let v = Pervasives.compare k1 k2 in if v = 0 then (KSet.compare) s1 s2 else v\n" +
                "    | (Int i1), (Int i2) -> Z.compare i1 i2\n" +
                "    | (Float (f1,e1,p1)), (Float (f2,e2,p2)) -> let v = e2 - e1 in if v = 0 then let v2 = p2 - p1 in if v2 = 0 then FR.compare f1 f2 else v2 else v\n" +
                "    | (String s1), (String s2) -> Pervasives.compare s1 s2\n" +
                "    | (Bool b1), (Bool b2) -> if b1 = b2 then 0 else if b1 then -1 else 1\n" +
                "    | Bottom, Bottom -> 0\n");
        for(long i : leftoverArities) {
            sb.append("    | KApply").append(i).append(" _, _ -> -1\n");
            sb.append("    | _, KApply").append(i).append(" _ -> 1\n");
        }

        sb.append("    | KToken(_, _), _ -> -1\n" +
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
                "end\n");
        sb.append("type normal_kitem = KApply of klabel * K.t list\n");
        sb.append("                  | KItem of K.kitem\n");
        sb.append("open K\n");
        sb.append("let normalize (k: kitem) : normal_kitem = match k with \n");
        for (long arity : leftoverArities) {
            sb.append("  | KApply").append(arity).append("(lbl");
            String conn = ",";
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i);
            }
            sb.append(") -> KApply (lbl, [");
            conn = "";
            for (int i = 0; i < arity; i++) {
                sb.append(conn);
                sb.append("k").append(i);
                conn = "; ";
            }
            sb.append("])\n");
        }
        sb.append("| v -> KItem v\n");
        sb.append("let denormalize (k: normal_kitem) : kitem = match k with \n");
        for (long arity : leftoverArities) {
            sb.append("  | KApply (lbl, [");
            String conn = "";
            for (int i = 0; i < arity; i++) {
                sb.append(conn);
                sb.append("k").append(i);
                conn = "; ";
            }
            sb.append("]) -> KApply").append(arity).append("(lbl");
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i);
            }
            sb.append(")\n");
        }
        sb.append("| KItem v -> v\ntype k = K.t\n");
        for (long arity : leftoverArities) {
            sb.append("let denormalize").append(arity).append(" ");
            printFunctionParams(sb, arity);
            sb.append(" : k list = match c with (");
            String conn = "";
            for (int i = 0; i < arity; i++) {
                sb.append(conn);
                sb.append("k").append(i);
                conn = ",";
            }
            sb.append(") -> [");
            conn = "";
            for (int i = 0; i < arity; i++) {
                sb.append(conn);
                sb.append("k").append(i);
                conn = "; ";
            }
            sb.append("]\n");

            sb.append("let normalize").append(arity);
            sb.append(" (c: k list) = match c with [");
            conn = "";
            for (int i = 0; i < arity; i++) {
                sb.append(conn);
                sb.append("k").append(i);
                conn = "; ";
            }
            sb.append("] -> (");
            conn = "";
            for (int i = 0; i < arity; i++) {
                sb.append(conn);
                sb.append("k").append(i);
                conn = ",";
            }
            sb.append(")\n");
        }

        Set<String> integerConstants = new HashSet<>();
        for (Rule r : iterable(mainModule.rules())) {
            integers(r.body(), integerConstants);
            integers(r.requires(), integerConstants);
        }
        for (String i : integerConstants) {
            sb.append("let ");
            encodeStringToIntConst(sb, i);
            sb.append(" = lazy (Int (Z.from_string \"" + i + "\"))\n");
        }
        return sb.toString();
    }

    private void integers(K term, Set<String> accum) {
        new VisitKORE() {
            @Override
            public Void apply(KToken k) {
                if (k.sort().equals(Sorts.Int())) {
                    accum.add(k.s());
                }
                return null;
            }
        }.apply(term);
    }

    private List<Tuple2<KLabel, Long>> mostUsedKLabels;
    private Set<Long> leftoverArities = new HashSet<>();

    private List<Tuple2<KLabel, Long>> printKType(StringBuilder sb) {
        sb.append("  and kitem = KToken of sort * string\n");
        sb.append("            | InjectedKLabel of klabel\n");
        sb.append("            | Map of sort * klabel * m\n");
        sb.append("            | List of sort * klabel * t list\n");
        sb.append("            | Set of sort * klabel * s\n");
        sb.append("            | Int of Z.t\n");
        sb.append("            | Float of FR.t * int * int\n");
        sb.append("            | String of string\n");
        sb.append("            | Bool of bool\n");
        sb.append("            | Bottom\n");
        class Holder {
            int i = 0;
        }
        Holder h = new Holder();
        BiMap<Tuple2<KLabel, Long>, Integer> uniqueIds = HashBiMap.create();
        forEachKLabel(t -> {
            //if (t._2() == 0) {
            //    StringBuilder cons = new StringBuilder();
            //    cons.append("Cons");
            //    encodeStringToAlphanumeric(cons, t._1().name());
            //    cons.append(t._2());
            //    klabels.put(t, "(" + cons.toString());
            //    sb.append("            | ").append(cons.toString()).append("\n");
            //} else {
                uniqueIds.put(t, h.i++);
            //}
        });
        int numRemaining = 246 - 10; // total per type - reserved by k
        /*mostUsedKLabels = stream(mainModule.klabelsDefinedInRules())
                .sorted((t1, t2) -> Integer.compare((int)t2._2(), (int)t1._2())) // sort by decreasing frequency of use
                .filter(t -> !isLookupKLabel(t._1()) && !t._1().name().equals("#KToken"))
                .map(t -> Tuple3.apply(t._1(), t._2(), uniqueIds.keySet().stream().filter(l -> l._1().equals(t._1())).findFirst().map(Tuple2::_2).orElse(0L))) // merge in arity
                .filter(t -> t._3() > 0)
                .filter(t -> !mainModule.attributesFor().apply(t._1()).contains(Attribute.FUNCTION_KEY))
                .limit(numRemaining) //grab top numRemaining tuples of arity > 0
                .map(t -> Tuple2.apply(t._1(), t._3())).collect(Collectors.toList());*/
        mostUsedKLabels = Collections.emptyList();
        forEachKLabel(t -> {
            //if (!mostUsedKLabels.contains(t) && t._2() != 0) {
                leftoverArities.add(t._2());
            //}
        });
  //      for (int i = mostUsedKLabels.size() - 1, j = 0; j < leftoverArities.size(); i--, j++) {
  //          mostUsedKLabels.remove(i);
  //      }
        forEachKLabel(t -> {
            if (mostUsedKLabels.contains(t)) {
                StringBuilder cons = new StringBuilder();
                cons.append("Cons");
                encodeStringToAlphanumeric(cons, t._1().name());
                cons.append(t._2());
                klabels.put(t, cons.toString() + "(");
                sb.append("            | ").append(cons.toString());
                String conn = " of ";
                for (int k = 0; k < t._2(); k++) {
                    sb.append(conn);
                    sb.append("t");
                    conn = " * ";
                }
                sb.append("\n");
            }
        });
        for (long arity : leftoverArities) {
            sb.append("            | KApply").append(arity).append(" of klabel");
            for (int i = 0; i < arity; i++) {
                sb.append(" * t");
            }
            sb.append("\n");
        }
        for (int i = 0; i * 246 < h.i; i++) {
            for (int j = 0; j < 246; j++) {
                int idx = i * 246 + j;
                Tuple2<KLabel, Long> t = uniqueIds.inverse().get(idx);
                if (t == null || mostUsedKLabels.contains(t))
                    continue;
                StringBuilder cons = new StringBuilder();
                cons.append("KApply").append(t._2()).append("(");
                encodeStringToIdentifier(cons, t._1());
                if (t._2() > 0)
                    cons.append(",");
                klabels.put(t, cons.toString());
            }
        }

        return mostUsedKLabels;
    }

    private BiMap<Tuple2<KLabel, Long>, String> klabels = HashBiMap.create();

    private void forEachKLabel(Consumer<Tuple2<KLabel, Long>> action) {
        for (KLabel label : iterable(mainModule.definedKLabels())) {
            if (isLookupKLabel(label) || label.name().equals("#KToken"))
                continue;
            stream(mainModule.productionsFor().apply(label)).map(p -> Tuple2.apply(p.klabel().get(), stream(p.items()).filter(pi -> pi instanceof NonTerminal).count())).distinct().forEach(action);
        }
    }

    public String definition() {
        StringBuilder sb = new StringBuilder();
        sb.append("open Prelude\nopen Constants\nopen Constants.K\nopen Gmp\n");
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
            String functionName = encodeStringToFunction(sb, functionLabel);
            int arity = getArity(functionLabel);
            printFunctionParams(sb, arity);
            sb.append(" (config: k) (guard: int) : k = let lbl = \n");
            encodeStringToIdentifier(sb, functionLabel);
            sb.append(" and sort = \n");
            encodeStringToIdentifier(sb, mainModule.sortFor().apply(functionLabel));
            sb.append(" in ");
            sb.append("match c with \n");
            String hook = mainModule.attributesFor().apply(functionLabel).<String>getOptional(Attribute.HOOK_KEY).orElse(".");
            String namespace = hook.substring(0, hook.indexOf('.'));
            String function = hook.substring(namespace.length() + 1);
            if (hookNamespaces.contains(namespace)) {
                sb.append("| _ -> try ").append(namespace).append(".hook_").append(function).append(" c lbl sort config freshFunction\n");
                sb.append("with Not_implemented -> match c with \n");
            } else if (!hook.equals(".")) {
                kem.registerCompilerWarning("missing entry for hook " + hook);
            }

            if (mainModule.attributesFor().apply(functionLabel).contains(Attribute.PREDICATE_KEY)) {
                Sort predicateSort = Sort(mainModule.attributesFor().apply(functionLabel).<String>get(Attribute.PREDICATE_KEY).get());
                Set<Sort> subsorts = stream(mainModule.definedSorts()).filter(s -> mainModule.subsorts().greaterThanEq(predicateSort, s)).collect(Collectors.toSet());
                for (Sort sort : subsorts) {
                    if (mainModule.sortAttributesFor().contains(sort)) {
                        String sortHook = mainModule.sortAttributesFor().apply(sort).<String>getOptional("hook").orElse("");
                        if (predicateRules.containsKey(sortHook)) {
                            sb.append("| ");
                            sb.append(predicateRules.get(sortHook).apply(sort));
                            sb.append("\n");
                        }
                    }
                }
            }

            convertFunction(functionRules.get(functionLabel).stream().sorted(this::sortFunctionRules).collect(Collectors.toList()),
                    sb, functionName, RuleType.FUNCTION);
            sb.append("| _ -> raise (Stuck [denormalize (KApply(lbl, (denormalize").append(arity).append(" c)))])\n");
            conn = "and ";
        }
        for (KLabel functionLabel : anywhereKLabels) {
            sb.append(conn);
            String functionName = encodeStringToFunction(sb, functionLabel);
            int arity = getArity(functionLabel);
            printFunctionParams(sb, arity);
            sb.append(" (config: k) (guard: int) : k = let lbl = \n");
            encodeStringToIdentifier(sb, functionLabel);
            sb.append(" in match c with \n");
            convertFunction(anywhereRules.get(functionLabel), sb, functionName, RuleType.ANYWHERE);
            sb.append("| _ -> [denormalize (KApply(lbl, (denormalize").append(arity).append(" c)))]\n");
            conn = "and ";
        }

        sb.append("and freshFunction (sort: string) (config: k) (counter: Z.t) : k = match sort with \n");
        for (Sort sort : iterable(mainModule.freshFunctionFor().keys())) {
            sb.append("| \"").append(sort.name()).append("\" -> (");
            KLabel freshFunction = mainModule.freshFunctionFor().apply(sort);
            encodeStringToFunction(sb, freshFunction);
            sb.append(" ([Int counter]) config (-1))\n");
        }
        sb.append("and eval (c: normal_kitem) (config: k) : k = match c with KApply(lbl, kl) -> (match lbl with \n");
        for (KLabel label : Sets.union(functions, anywhereKLabels)) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            encodeStringToFunction(sb, label);
            int arity = getArity(label);
            sb.append(" (normalize").append(arity).append(" kl) config (-1)\n");
        }
        sb.append("| _ -> [denormalize c])\n");
        sb.append("| _ -> [denormalize c]\n");
        functions.stream().filter(lbl -> !mainModule.attributesFor().apply(lbl).contains(Attribute.IMPURE_KEY) && stream(mainModule.productionsFor().apply(lbl)).filter(p -> p.arity() == 0).findAny().isPresent()).forEach(lbl -> {
            sb.append("and const");
            encodeStringToAlphanumeric(sb, lbl.name());
            sb.append(" : k Lazy.t = lazy (");
            encodeStringToFunction(sb, lbl);
            sb.append(" () [Bottom] (-1))\n");
        });
        sb.append("let rec lookups_step (c: k) (config: k) (guard: int) : k = match c with \n");
        List<Rule> sortedRules = stream(mainModule.rules())
                .sorted((r1, r2) -> ComparisonChain.start()
                        .compareTrueFirst(r1.att().contains("structural"), r2.att().contains("structural"))
                        .compareFalseFirst(r1.att().contains("owise"), r2.att().contains("owise"))
                        .compareFalseFirst(indexesPoorly(r1), indexesPoorly(r2))
                        .result())
                .filter(r -> !functionRules.values().contains(r) && !r.att().contains(Attribute.MACRO_KEY) && !r.att().contains(Attribute.ANYWHERE_KEY))
                .collect(Collectors.toList());
        Map<Boolean, List<Rule>> groupedByLookup = sortedRules.stream()
                .collect(Collectors.groupingBy(this::hasLookups));
        convert(groupedByLookup.get(true), sb, "lookups_step", RuleType.REGULAR, 0);
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
        sb.append("| _ -> lookups_step c c (-1)\n");
        sb.append(postlude);
        return sb.toString();
    }

    private int getArity(KLabel functionLabel) {
        Set<Integer> arities = stream(mainModule.productionsFor().apply(functionLabel)).map(Production::arity).collect(Collectors.toSet());
        if (arities.size() > 1) {
            throw KEMException.compilerError("KLabel " + functionLabel + " has multiple productions with differing arities: " + mainModule.productionsFor().apply(functionLabel));
        }
        assert arities.size() == 1;
        int arity = arities.iterator().next();
        return arity;
    }

    private void printFunctionParams(StringBuilder sb, long arity) {
        if (arity == 0)
            sb.append(" (c: unit)");
        else {
            sb.append(" (c: ");
            String conn2 = "";
            for (int i = 0; i < arity; i++) {
                sb.append(conn2);
                sb.append("k");
                conn2 = " * ";
            }
            sb.append(")");
        }
    }

    private void convertFunction(List<Rule> rules, StringBuilder sb, String functionName, RuleType type) {
        int ruleNum = 0;
        for (Rule r : rules) {
            if (hasLookups(r)) {
                ruleNum = convert(Collections.singletonList(r), sb, functionName, type, ruleNum);
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

    private void encodeStringToCons(StringBuilder sb, KLabel name, long arity) {
        sb.append(klabels.get(Tuple2.apply(name, arity)));
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

    private static String encodeStringToIdentifier(KLabel name) {
        StringBuilder sb = new StringBuilder();
        encodeStringToIdentifier(sb, name);
        return sb.toString();
    }


    private static String encodeStringToFunction(StringBuilder sb, KLabel lbl) {
        StringBuilder sb2 = new StringBuilder();
        sb2.append("eval");
        encodeStringToAlphanumeric(sb2, lbl.name());
        sb.append(sb2);
        return sb2.toString();
    }

    private static String encodeStringToIntConst(String i) {
        return encodeStringToIntConst(new StringBuilder(), i);
    }

    private static String encodeStringToIntConst(StringBuilder sb, String i) {
        StringBuilder sb2 = new StringBuilder();
        sb2.append("int");
        encodeStringToAlphanumeric(sb2, i);
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

    private enum RuleType {
        FUNCTION, ANYWHERE, REGULAR, PATTERN
    }

    private static class VarInfo {
        final SetMultimap<KVariable, String> vars;
        final Map<String, KLabel> listVars;
        final Map<K, String> termCache;

        VarInfo() { this(HashMultimap.create(), new HashMap<>(), new HashMap<>()); }

        VarInfo(VarInfo vars) {
            this(HashMultimap.create(vars.vars), new HashMap<>(vars.listVars), new HashMap<>(vars.termCache));
        }

        VarInfo(SetMultimap<KVariable, String> vars, Map<String, KLabel> listVars, Map<K, String> termCache) {
            this.vars = vars;
            this.listVars = listVars;
            this.termCache = termCache;
        }
    }

    private int convert(List<Rule> rules, StringBuilder sb, String functionName, RuleType ruleType, int ruleNum) {
        NormalizeVariables t = new NormalizeVariables();
        Map<AttCompare, List<Rule>> grouping = rules.stream().collect(
                Collectors.groupingBy(r -> new AttCompare(t.normalize(RewriteToTop.toLeft(r.body())), "sort")));
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
            sb.append(" when guard < ").append(ruleNum);
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
                globalVars.termCache.remove(KToken("dummy", Sort("Dummy")));
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
                        sb.append(" when guard < ").append(ruleNum);
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
            sb.append(" when guard < ").append(ruleNum);

            convertComment(r, sb);
            List<Lookup> lookups = convertLookups(r.requires(), globalVars, functionName, ruleNum, false);
            String suffix = convertSideCondition(sb, r.requires(), globalVars, lookups, lookups.size() > 0);
            sb.append(" -> ");
            convertRHS(sb, ruleType, RewriteToTop.toRight(r.body()), globalVars, suffix);
            ruleNum++;
        }
        return ruleNum;
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
        Visitor visitor = convert(sb, false, vars, false, false);
        if (type == RuleType.ANYWHERE || type == RuleType.FUNCTION) {
            KApply kapp = (KApply) ((KSequence) left).items().get(0);
            sb.append("(");
            visitor.applyTuple(kapp.klist().items());
            sb.append(")");
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
                boolean isList = isList(var, false, true, vars, false);
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
            convert(sb, true, vars, false, type == RuleType.ANYWHERE).apply(right);
        }
        if (type == RuleType.ANYWHERE) {
            sb.append(" with [item] -> eval (normalize item) config)");
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
        convert(sb, true, vars, true, false).apply(requires);
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

    private int choiceCounter = 0;

    private List<Lookup> convertLookups(K requires, VarInfo vars, String functionName, int ruleNum, boolean hasMultiple) {
        List<Lookup> results = new ArrayList<>();
        Holder h = new Holder();
        h.first = hasMultiple;
        h.reapply = "(" + functionName + " c config " + ruleNum + ")";
        new VisitKORE() {
            @Override
            public Void apply(KApply k) {
                if (k.klabel().name().equals("#match")) {
                    if (k.klist().items().size() != 2) {
                        throw KEMException.internalError("Unexpected arity of lookup: " + k.klist().size(), k);
                    }
                    StringBuilder sb = new StringBuilder();
                    sb.append(" -> (let e = ");
                    convert(sb, true, vars, false, false).apply(k.klist().items().get(1));
                    sb.append(" in ");
                    if (h.first) {
                        sb.append("let rec stepElt = fun guard -> ");
                    }
                    sb.append("match e with \n");
                    sb.append("| [Bottom] -> ").append(h.reapply).append("\n");
                    String prefix = sb.toString();
                    sb = new StringBuilder();
                    sb.append("| ");
                    convert(sb, false, vars, false, false).apply(k.klist().items().get(0));
                    String pattern = sb.toString();
                    String suffix = "| _ -> " + h.reapply;
                    if (h.first) {
                        suffix += " in stepElt (-1)";
                        h.reapply = "(stepElt " + ruleNum + ")";
                    }
                    suffix += ")";
                    results.add(new Lookup(prefix, pattern, suffix));
                    h.first = false;
                } else if (k.klabel().name().equals("#setChoice")) {
                    choose(k, "| [Set (_,_,collection)] -> let choice = (KSet.fold (fun e result -> ");
                } else if (k.klabel().name().equals("#mapChoice")) {
                    choose(k, "| [Map (_,_,collection)] -> let choice = (KMap.fold (fun e v result -> ");
                }
                return super.apply(k);
            }

            private void choose(KApply k, String choiceString) {
                if (k.klist().items().size() != 2) {
                    throw KEMException.internalError("Unexpected arity of choice: " + k.klist().size(), k);
                }
                vars.termCache.put(k.klist().items().get(0), "e" + choiceCounter);
                StringBuilder sb = new StringBuilder();
                sb.append(" -> (match ");
                convert(sb, true, vars, false, false).apply(k.klist().items().get(1));
                sb.append(" with \n");
                sb.append(choiceString);
                if (h.first) {
                    sb.append("let rec stepElt = fun guard -> ");
                }
                sb.append("if (compare result [Bottom]) = 0 then (match e with ");
                String prefix = sb.toString();
                sb = new StringBuilder();
                String suffix2 = "| _ -> [Bottom]) else result" + (h.first ? " in stepElt (-1)" : "") + ") collection [Bottom]) in if (compare choice [Bottom]) = 0 then " + h.reapply + " else choice";
                String suffix = suffix2 + "| _ -> " + h.reapply + ")";
                if (h.first) {
                    h.reapply = "(stepElt " + ruleNum + ")";
                } else {
                    h.reapply = "[Bottom]";
                }
                sb.append("| ");
                convert(sb, false, vars, false, false).apply(k.klist().items().get(0));
                sb.append(" as e").append(choiceCounter++);
                String pattern = sb.toString();
                results.add(new Lookup(prefix, pattern, suffix));
                h.first = false;
            }
        }.apply(requires);
        return results;
    }

    private String convert(VarInfo vars) {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<KVariable, Collection<String>> entry : vars.vars.asMap().entrySet()) {
            Collection<String> nonLinearVars = entry.getValue();
            if (nonLinearVars.size() < 2) {
                continue;
            }
            Iterator<String> iter = nonLinearVars.iterator();
            String last = iter.next();
            while (iter.hasNext()) {
                //handle nonlinear variables in pattern
                String next = iter.next();
                if (!isList(entry.getKey(), false, true, vars, false)) {
                    sb.append("((compare_kitem ");
                } else{
                    sb.append("((compare ");
                }
                applyVarRhs(last, sb, vars.listVars.get(last));
                sb.append(" ");
                applyVarRhs(next, sb, vars.listVars.get(next));
                sb.append(") = 0)");
                last = next;
                sb.append(" && ");
            }
        }
        sb.append("true");
        return sb.toString();
    }

    private void applyVarRhs(KVariable v, StringBuilder sb, VarInfo vars) {
        applyVarRhs(vars.vars.get(v).iterator().next(), sb, vars.listVars.get(vars.vars.get(v).iterator().next()));
    }

    private void applyVarRhs(String varOccurrance, StringBuilder sb, KLabel listVar) {
        if (listVar != null) {
            sb.append("(List (");
            encodeStringToIdentifier(sb, mainModule.sortFor().apply(listVar));
            sb.append(", ");
            encodeStringToIdentifier(sb, listVar);
            sb.append(", ");
            sb.append(varOccurrance);
            sb.append("))");
        } else {
            sb.append(varOccurrance);
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

    private Visitor convert(StringBuilder sb, boolean rhs, VarInfo vars, boolean useNativeBooleanExp, boolean anywhereRule) {
        return new Visitor(sb, rhs, vars, useNativeBooleanExp, anywhereRule);
    }

    private class Visitor extends VisitKORE {
        private final StringBuilder sb;
        private final boolean rhs;
        private final VarInfo vars;

        public Visitor(StringBuilder sb, boolean rhs, VarInfo vars, boolean useNativeBooleanExp, boolean anywhereRule) {
            this.sb = sb;
            this.rhs = rhs;
            this.vars = vars;
            this.inBooleanExp = useNativeBooleanExp;
            this.topAnywherePre = anywhereRule;
            this.topAnywherePost = anywhereRule;
        }

        private boolean inBooleanExp;
        private boolean topAnywherePre;
        private boolean topAnywherePost;

        @Override
        public Void apply(KApply k) {
            if (k.klabel() instanceof KVariable && rhs) {
                boolean stack = inBooleanExp;
                inBooleanExp = false;
                if (stack) {
                    sb.append("(isTrue ");
                }
                sb.append("(eval (");
                applyKLabel(k);
                sb.append(") config)");
                if (stack) {
                    sb.append(")");
                }
                inBooleanExp = stack;
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
            } else if (functions.contains(k.klabel()) || (anywhereKLabels.contains(k.klabel()) && rhs && !topAnywherePre)) {
                applyFunction(k);
            } else {
                topAnywherePre = false;
                if (k.klabel() instanceof KVariable) {
                    sb.append("KApply").append(k.klist().size()).append("(");
                    apply(k.klabel());
                    sb.append(",");
                    applyTuple(k.klist().items());
                    sb.append(")");
                } else {
                    encodeStringToCons(sb, k.klabel(), k.klist().items().size());
                    if (k.klist().size() > 0) {
                        applyTuple(k.klist().items());
                    }
                    sb.append(")");
                }
            }
            return null;
        }

        private void applyTuple(List<K> items) {
            for (int i = 0; i < items.size(); i++) {
                K item = items.get(i);
                apply(item);
                if (i != items.size() - 1) {
                    sb.append(",");
                }
            }
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
            if ((hook.equals("BOOL.and") || hook.equals("BOOL.andThen"))) {
                assert k.klist().items().size() == 2;
                if (!stack) {
                    sb.append("[Bool (");
                }
                inBooleanExp = true;
                sb.append("(");
                apply(k.klist().items().get(0));
                sb.append(") && (");
                apply(k.klist().items().get(1));
                sb.append(")");
                if (!stack) {
                    sb.append(")]");
                }
            } else if ((hook.equals("BOOL.or") || hook.equals("BOOL.orElse"))) {
                assert k.klist().items().size() == 2;
                if (!stack) {
                    sb.append("[Bool (");
                }
                inBooleanExp = true;
                sb.append("(");
                apply(k.klist().items().get(0));
                sb.append(") || (");
                apply(k.klist().items().get(1));
                sb.append(")");
                if (!stack) {
                    sb.append(")]");
                }
            } else if (hook.equals("BOOL.not")) {
                assert k.klist().items().size() == 1;
                if (!stack) {
                    sb.append("[Bool (");
                }
                inBooleanExp = true;
                sb.append("(not (");
                apply(k.klist().items().get(0));
                sb.append("))");
                if (!stack) {
                    sb.append(")]");
                }
            } else if (hook.equals("KEQUAL.ite")) {
                assert k.klist().items().size() == 3;
                inBooleanExp = true;
                sb.append("(if (");
                apply(k.klist().items().get(0));
                inBooleanExp = stack;
                sb.append(") then (");
                apply(k.klist().items().get(1));
                sb.append(") else (");
                apply(k.klist().items().get(2));
                sb.append("))");
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
                        encodeStringToIdentifier(sb, collectionLabel);
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
                                vars.listVars.put(varName, collectionLabel);
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
                    if (s.equals(Sorts.K()) && k.klist().items().size() == 1) {
                        apply(BooleanUtils.TRUE);
                        return;
                    }
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
                if (k.klist().items().size() > 0 || mainModule.attributesFor().apply(k.klabel()).contains(Attribute.IMPURE_KEY)) {
                    encodeStringToFunction(sb, k.klabel());
                    sb.append("(");
                    applyTuple(k.klist().items());
                    sb.append(") config (-1)");
                } else {
                    sb.append("Lazy.force const");
                    encodeStringToAlphanumeric(sb, k.klabel().name());
                }
                sb.append(")");
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
            if (inBooleanExp && k.sort().equals(Sorts.Bool())) {
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
            sb.append(enquoteString(k.s()));
            sb.append(")");
            return null;
        }

        @Override
        public Void apply(KVariable k) {
            if (inBooleanExp) {
                sb.append("(isTrue [");
            }
            if (rhs) {
                applyVarRhs(k, sb, vars);
            } else {
                applyVarLhs(k, sb, vars);
            }
            if (inBooleanExp) {
                sb.append("])");
            }
            return null;
        }

        @Override
        public Void apply(KSequence k) {
            if (k.items().size() == 1 && inBooleanExp) {
                apply(k.items().get(0));
                return null;
            }
            if (vars.termCache.containsKey(k) && rhs) {
                sb.append(vars.termCache.get(k));
                return null;
            }
            sb.append("(");
            if (!rhs) {
                for (int i = 0; i < k.items().size() - 1; i++) {
                    if (isList(k.items().get(i), false, rhs, vars, topAnywherePost)) {
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
                boolean stack = topAnywherePre;
                apply(item);
                if (i != items.size() - 1) {
                    if (isList(item, klist, rhs, vars, stack)) {
                        sb.append(" @ ");
                    } else {
                        sb.append(" :: ");
                    }
                } else {
                    if (!isList(item, klist, rhs, vars, stack)) {
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
        if (vars.vars.containsKey(k)) {
            String varName = vars.vars.get(k).iterator().next();
            if (vars.listVars.containsKey(varName)) {
                return vars.listVars.get(varName).name();
            }
        }
        return k.att().<String>getOptional(Attribute.SORT_KEY).orElse("K");
    }

    private boolean isLookupKLabel(KLabel k) {
        return k.name().equals("#match") || k.name().equals("#mapChoice") || k.name().equals("#setChoice");
    }

    private boolean isLookupKLabel(KApply k) {
        return isLookupKLabel(k.klabel());
    }

    private boolean isList(K item, boolean klist, boolean rhs, VarInfo vars, boolean anywhereRule) {
        return !klist && ((item instanceof KVariable && getSortOfVar((KVariable)item, vars).equals("K")) || item instanceof KSequence
                || (item instanceof KApply && (functions.contains(((KApply) item).klabel()) || (((anywhereKLabels.contains(((KApply) item).klabel()) && !anywhereRule) || ((KApply) item).klabel() instanceof KVariable) && rhs))))
                && !(!rhs && item instanceof KApply && collectionFor.containsKey(((KApply) item).klabel()));
    }

}
