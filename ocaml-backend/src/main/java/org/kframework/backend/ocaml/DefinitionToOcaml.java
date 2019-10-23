// Copyright (c) 2015-2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.

package org.kframework.backend.ocaml;

import com.google.common.base.Joiner;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.BiMap;
import com.google.common.collect.ComparisonChain;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import org.apache.commons.collections15.ListUtils;
import org.apache.commons.lang3.mutable.MutableBoolean;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.*;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.Assoc;
import org.kframework.kore.AttCompare;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.VisitK;
import org.kframework.kore.TransformK;
import org.kframework.krun.KRun;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.outer.Outer;
import org.kframework.unparser.ToBinary;
import org.kframework.unparser.ToKast;
import org.kframework.utils.StringUtil;
import org.kframework.utils.algorithms.SCCTarjan;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Function1;
import scala.Tuple2;
import scala.Tuple3;

import java.io.File;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Queue;
import java.util.regex.Pattern;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class DefinitionToOcaml implements Serializable {

    private transient final KExceptionManager kem;
    private transient final FileUtil files;
    private transient final GlobalOptions globalOptions;
    private transient final KompileOptions kompileOptions;
    private transient ExpandMacros expandMacros;
    private transient ConvertDataStructureToLookup convertDataStructure;
    private boolean threadCellExists;
    private transient Rule exitCodePattern;
    public OcamlOptions options;
    private Map<String, List<KLabel>> klabelsForEachPredicate;

    public DefinitionToOcaml(
            KExceptionManager kem,
            FileUtil files,
            GlobalOptions globalOptions,
            KompileOptions kompileOptions,
            OcamlOptions options) {
        this.kem = kem;
        this.files = files;
        this.globalOptions = globalOptions;
        this.kompileOptions = kompileOptions;
        this.sortHooks = defSortHooks;
        this.options = options;
    }

    public static final ImmutableSet<String> hookNamespaces;
    private transient ImmutableMap<String, Function<String, String>> sortHooks;
    public static final ImmutableMap<String, Function<String, String>> defSortHooks;
    public static final ImmutableMap<String, Function<String, String>> userSortHooks;
    public static final ImmutableMap<String, Function<Sort, String>> sortVarHooks;
    public static final ImmutableMap<String, Function<Sort, String>> predicateRules;

    static {
        ImmutableSet.Builder<String> builder = ImmutableSet.builder();
        builder.add("BOOL").add("FLOAT").add("INT").add("IO").add("K").add("KEQUAL").add("KREFLECTION").add("LIST");
        builder.add("MAP").add("SET").add("STRING").add("ARRAY").add("BUFFER").add("BYTES");
        hookNamespaces = builder.build();
    }

    private static String stringBufferConstant(String s) {
        String string = StringUtil.unquoteKString(StringUtil.unquoteKString("\"" + s + "\""));
        return "(StringBuffer (let buf = Buffer.create " + string.length() + " in Buffer.add_string buf " + enquoteString(string) + "; buf))";
    }

    static {
        ImmutableMap.Builder<String, Function<String, String>> builder = ImmutableMap.builder();
        builder.put("BOOL.Bool", s -> "(Bool " + s + ")");
        builder.put("INT.Int", s -> "(Int (Z.of_string \"" +  s + "\"))");
        builder.put("FLOAT.Float", s -> {
            FloatBuiltin f = FloatBuiltin.of(s);
            return "(round_to_range(Float ((Gmp.FR.from_string_prec_base " + f.precision() + " Gmp.GMP_RNDN 10 \"" + f.value() + "\"), " + f.exponent() + ", " + f.precision() + ")))";
        });
        builder.put("STRING.String", s -> "(String " + enquoteString(StringUtil.unquoteKString(s)) + ")");
        builder.put("BYTES.Bytes", s -> "(Bytes (Bytes.of_string " + enquoteString(StringUtil.unquoteKString(s)) + "))");
        builder.put("BUFFER.StringBuffer", DefinitionToOcaml::stringBufferConstant);
        userSortHooks = builder.build();

        builder = ImmutableMap.builder();
        builder.put("BOOL.Bool", s -> "(Bool " + s + ")");
        builder.put("INT.Int", s -> "(Lazy.force " + encodeStringToIntConst(s) + ")");
        builder.put("FLOAT.Float", s -> {
            FloatBuiltin f = FloatBuiltin.of(s);
            return "(round_to_range(Float ((Gmp.FR.from_string_prec_base " + f.precision() + " Gmp.GMP_RNDN 10 \"" + f.value() + "\"), " + f.exponent() + ", " + f.precision() + ")))";
        });
        builder.put("STRING.String", s -> "(String " + enquoteString(StringUtil.unquoteKString(s)) + ")");
        builder.put("BYTES.Bytes", s -> "(Bytes (Bytes.of_string " + enquoteString(StringUtil.unquoteKString(s)) + "))");
        builder.put("BUFFER.StringBuffer", DefinitionToOcaml::stringBufferConstant);
        defSortHooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, Function<Sort, String>> builder = ImmutableMap.builder();
        builder.put("BOOL.Bool", s -> "Bool _");
        builder.put("INT.Int", s -> "Int _");
        builder.put("FLOAT.Float", s -> "Float _");
        builder.put("STRING.String", s -> "String _");
        builder.put("BYTES.Bytes", s -> "Bytes _");
        builder.put("BUFFER.StringBuffer", s -> "StringBuffer _");
        builder.put("LIST.List", s -> "List (" + encodeStringToIdentifier(s) + ",_,_)");
        builder.put("ARRAY.Array", s -> "Array (" + encodeStringToIdentifier(s) + ",_,_)");
        builder.put("MAP.Map", s -> "Map (" + encodeStringToIdentifier(s) + ",_,_)");
        builder.put("SET.Set", s -> "Set (" + encodeStringToIdentifier(s) + ",_,_)");
        sortVarHooks = builder.build();
    }

    static {
        ImmutableMap.Builder<String, Function<Sort, String>> builder = ImmutableMap.builder();
        builder.put("K.K", s -> "_ -> [Bool true]");
        builder.put("K.KItem", s -> "[_] -> [Bool true] | _ -> [Bool false]");
        builder.put("INT.Int", s -> "[Int _] -> [Bool true]");
        builder.put("FLOAT.Float", s -> "[Float _] -> [Bool true]");
        builder.put("STRING.String", s -> "[String _] -> [Bool true]");
        builder.put("BYTES.Bytes", s -> "[Bytes _] -> [Bool true]");
        builder.put("BUFFER.StringBuffer", s -> "[StringBuffer _] -> [Bool true]");
        builder.put("BOOL.Bool", s -> "[Bool _] -> [Bool true]");
        builder.put("MAP.Map", s -> "[Map (s,_,_)] when (s = " + encodeStringToIdentifier(s) + ") -> [Bool true]");
        builder.put("SET.Set", s -> "[Set (s,_,_)] when (s = " + encodeStringToIdentifier(s) + ") -> [Bool true]");
        builder.put("LIST.List", s -> "[List (s,_,_)] when (s = " + encodeStringToIdentifier(s) + ") -> [Bool true]");
        builder.put("ARRAY.Array", s -> "[Array (s,_,_)] when (s = " + encodeStringToIdentifier(s) + ") -> [Bool true]");
        predicateRules = builder.build();
    }


    private Module mainModule;
    private Map<KLabel, KLabel> collectionFor;
    private Set<KLabel> filteredMapConstructors;
    private Rule matchThreadSet, rewriteThreadSet;
    private Rule makeStuck, makeUnstuck;

    public void initialize(DefinitionToOcaml serialized, CompiledDefinition def) {
        mainModule = serialized.mainModule;
        collectionFor = serialized.collectionFor;
        filteredMapConstructors = serialized.filteredMapConstructors;
        matchThreadSet = serialized.matchThreadSet;
        rewriteThreadSet = serialized.rewriteThreadSet;
        makeStuck = serialized.makeStuck;
        makeUnstuck = serialized.makeUnstuck;
        functions = serialized.functions;
        anywhereKLabels = serialized.anywhereKLabels;
        options = serialized.options;
        constants = serialized.constants;
        realStepFunctions = serialized.realStepFunctions;
        if (serialized.expandMacros == null) {
            serialized.expandMacros = ExpandMacros.fromMainModule(def.executionModule(), files, kompileOptions, false);
        }
        if (serialized.convertDataStructure == null) {
            serialized.convertDataStructure = new ConvertDataStructureToLookup(def.executionModule(), true);
        }
        expandMacros = serialized.expandMacros;
        convertDataStructure = serialized.convertDataStructure;
        threadCellExists = serialized.threadCellExists;
        if (serialized.exitCodePattern == null) {
            serialized.exitCodePattern = def.exitCodePattern;
        }
        exitCodePattern = serialized.exitCodePattern;
        sortHooks = userSortHooks;
        klabelsForEachPredicate = serialized.klabelsForEachPredicate;
    }

    private boolean containsThreadCell(CompiledDefinition def) {
        return stream(def.executionModule().productions())
                    .anyMatch(p -> (p.att().contains("thread") && p.att().contains("cell")));
    }
    public void initialize(CompiledDefinition def) {
        Function1<Module, Module> generatePredicates = new GenerateSortPredicateRules(false)::gen;
        this.convertDataStructure = new ConvertDataStructureToLookup(def.executionModule(), true);
        ModuleTransformer convertLookups = ModuleTransformer.fromSentenceTransformer(convertDataStructure::convert, "convert data structures to lookups");
        ModuleTransformer liftToKSequence = ModuleTransformer.fromSentenceTransformer(new LiftToKSequence()::lift, "lift K into KSequence");
        this.expandMacros = ExpandMacros.fromMainModule(def.executionModule(), files, kompileOptions, false);
        ModuleTransformer expandMacros = ModuleTransformer.fromSentenceTransformer(this.expandMacros::expand, "expand macro rules");
        ModuleTransformer deconstructInts = ModuleTransformer.fromSentenceTransformer(new DeconstructIntegerAndFloatLiterals()::convert, "remove matches on integer literals in left hand side");
        this.threadCellExists = containsThreadCell(def);
        this.exitCodePattern = def.exitCodePattern;
        ModuleTransformer splitThreadCell = this.threadCellExists ?
                                            ModuleTransformer.fromSentenceTransformer(new SplitThreadsCell(def.executionModule())::convert, "split threads cell into thread local and global") :
                                            ModuleTransformer.fromSentenceTransformer(s -> s, "identity function -- no transformation");
        ModuleTransformer preprocessKLabelPredicates = ModuleTransformer.fromSentenceTransformer(new PreprocessKLabelPredicates(def.executionModule())::convert, "preprocess klabel predicates");
        ModuleTransformer removePolyKLabels = ModuleTransformer.fromSentenceTransformer(Kompile::removePolyKLabels, "remove poly klabels");
        Sentence thread = Production(KLabel("#Thread"), Sorts.KItem(), Seq(
                Terminal("#Thread"), Terminal("("),
                NonTerminal(Sorts.K()), Terminal(","),
                NonTerminal(Sorts.K()), Terminal(","),
                NonTerminal(Sorts.K()), Terminal(","),
                NonTerminal(Sorts.K()), Terminal(")")));
        Sentence bottom = Production(KLabel("#Bottom"), Sorts.KItem(), Seq(Terminal("#Bottom")));
        Sentence threadLocal = Production(KLabel("#ThreadLocal"), Sorts.KItem(), Seq(Terminal("#ThreadLocal")));
        Function1<Module, Module> pipeline = removePolyKLabels
                .andThen(preprocessKLabelPredicates)
                .andThen(splitThreadCell)
                .andThen(mod -> Module(mod.name(), mod.imports(),
                        Stream.concat(stream(mod.localSentences()),
                                Stream.<Sentence>of(thread, bottom, threadLocal)).collect(org.kframework.Collections.toSet()), mod.att()))
                .andThen(convertLookups)
                .andThen(expandMacros)
                .andThen(deconstructInts)
                .andThen(generatePredicates)
                .andThen(liftToKSequence);
        mainModule = pipeline.apply(def.executionModule());
        collectionFor = ConvertDataStructureToLookup.collectionFor(mainModule);
        filteredMapConstructors = ConvertDataStructureToLookup.filteredMapConstructors(mainModule);

        Set<KLabel> threadKLabels = stream(mainModule.attributesFor()).filter(p -> p._2().contains("thread")).map(Tuple2::_1).collect(Collectors.toSet());
        if (threadKLabels.size() == 0) {
            this.matchThreadSet = null;
            this.rewriteThreadSet = null;
        } else {
            if (threadKLabels.size() != 1) {
                throw KEMException.criticalError("Must have only one klabel with the \"thread\" attribute. Found: " + threadKLabels);
            }
            Rule matchThreadSet = Rule(IncompleteCellUtils.make(threadKLabels.iterator().next(), false, KVariable("Threads"), false), BooleanUtils.TRUE, BooleanUtils.TRUE);
            this.matchThreadSet = convert(new Kompile(kompileOptions, files, kem).compileRule(def.kompiledDefinition, matchThreadSet));
            Rule rewriteThreadSet = Rule(IncompleteCellUtils.make(threadKLabels.iterator().next(), false, KRewrite(KVariable("Threads"), KVariable("NewThreads")), false), BooleanUtils.TRUE, BooleanUtils.TRUE);
            this.rewriteThreadSet = convert(new Kompile(kompileOptions, files, kem).compileRule(def.kompiledDefinition, rewriteThreadSet));
            this.rewriteThreadSet = Rule(new TransformK() { public K apply(KVariable var) { return KVariable(var.name(), var.att().remove(Sort.class)); } }.apply(this.rewriteThreadSet.body()),
                    this.rewriteThreadSet.requires(), this.rewriteThreadSet.ensures());
        }
        KLabel stratCell = KLabel("<s>");
        if (mainModule.definedKLabels().contains(stratCell)) {
            Rule makeStuck = Rule(IncompleteCellUtils.make(stratCell, false, KRewrite(KSequence(), KApply(KLabel("#STUCK"))), true), BooleanUtils.TRUE, BooleanUtils.TRUE);
            Rule makeUnstuck = Rule(IncompleteCellUtils.make(stratCell, false, KRewrite(KApply(KLabel("#STUCK")), KSequence()), true), BooleanUtils.TRUE, BooleanUtils.TRUE);
            this.makeStuck = convert(new Kompile(kompileOptions, files, kem).compileRule(def.kompiledDefinition, makeStuck));
            this.makeUnstuck = convert(new Kompile(kompileOptions, files, kem).compileRule(def.kompiledDefinition, makeUnstuck));
        } else {
            this.makeStuck = null;
            this.makeUnstuck = null;
        }
    }

    public Rule convert(Rule r) {
        Function1<Sentence, Sentence> convertLookups = new ConvertDataStructureToLookup(this.convertDataStructure)::convert;
        Function1<Sentence, Sentence> liftToKSequence = new LiftToKSequence()::lift;
        Function1<Sentence, Sentence> deconstructInts = new DeconstructIntegerAndFloatLiterals()::convert;
        Function1<Sentence, Sentence> expandMacros = this.expandMacros::expand;
        return (Rule) convertLookups
                .andThen(deconstructInts)
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
                if (codepoint < 10) {
                    result.append("\\00");
                    result.append(codepoint);
                } else if (codepoint < 100) {
                    result.append("\\0");
                    result.append(codepoint);
                } else {
                    result.append("\\");
                    result.append(codepoint);
                }
            }
        }
        result.append(delimiter);
        return result.toString();
    }

    public static String enquoteString(byte[] value) {
        char delimiter = '"';
        final int length = value.length;
        StringBuilder result = new StringBuilder();
        result.append(delimiter);
        for (int offset = 0, codepoint; offset < length; offset++) {
            codepoint = Byte.toUnsignedInt(value[offset]);
            if (codepoint == delimiter) {
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
            } else if (codepoint < 16){
                result.append("\\x0");
                result.append(Integer.toHexString(codepoint));
            } else if (codepoint < 32 || codepoint >= 127) {
                result.append("\\x");
                result.append(Integer.toHexString(codepoint));
            } else
                result.append((char)codepoint);
        }
        result.append(delimiter);
        return result.toString();
    }

    public String execute(K k, int depth, String file) {
        StringBuilder sb = new StringBuilder();
        ocamlProgramHeader(sb, true);
        ocamlTermInput(new KRun.InitialConfiguration(k), sb); //declares input
        ocamlOpenFile("out", file, sb); //declares out
        runAndPrint(depth, sb); //calls run and prints to out
        return sb.toString();
    }

    public String match(K k, Rule r, String file) {
        StringBuilder sb = new StringBuilder();
        ocamlProgramHeader(sb, true);
        ocamlMatchPattern(r, sb); //declares try_match
        ocamlTermInput(new KRun.InitialConfiguration(k), sb); //declares input
        ocamlOpenFile("subst", file, sb); //declares subst
        sb.append("let res = input\n");
        matchPatternAndPrint(sb); //calls try_match and prints to subst
        return sb.toString();
    }

    private void ocamlMatchPattern(Rule r, StringBuilder sb) {
        if (r == null) {
            // no exit code pattern
            sb.append("let try_match (c: k) (config: k) (guard: int) : k Subst.t = Subst.singleton \"_\" [Int Z.zero]\n");
            return;
        }
        if (hasLookups(r)) {
            sb.append("let rec ");
        } else {
            sb.append("let ");
        }
        sb.append("try_match (c: k) (config: k) (guard: int) : k Subst.t = match c with \n");
        convertFunction(Collections.singletonList(convert(r)), sb, "try_match", RuleType.PATTERN);
        sb.append("| _ -> raise(Stuck c)\n");
    }

    public String executeAndMatch(K k, int depth, Rule r, String file, String substFile) {
        StringBuilder sb = new StringBuilder();
        ocamlProgramHeader(sb, true);
        ocamlMatchPattern(r, sb);  //declares try_match
        ocamlTermInput(new KRun.InitialConfiguration(k), sb);  //declares input
        ocamlOpenFile("out", file, sb); //declares out
        ocamlOpenFile("subst", substFile, sb); //declares subst
        runAndPrint(depth, sb); //calls run and prints to out
        matchPatternAndPrint(sb); //calls try_match and prints to subst
        return sb.toString();
    }

    private void constructRun(StringBuilder sb, String depth) {
        if (this.threadCellExists) {
            sb.append("run");
        } else {
            sb.append("run_no_thread_opt");
        }
        sb.append("(input) (").append(depth).append(") ");
    }

    public String interpreter() {
        StringBuilder sb = new StringBuilder();
        ocamlProgramHeader(sb, true);
        ocamlMatchPattern(exitCodePattern, sb);  //declares try_match
        sb.append("let input, depth, out = Makeconfig.parse ()\n");
        sb.append("let res, _ = ");
        if (this.threadCellExists) {
            sb.append("run");
        } else {
            sb.append("run_no_thread_opt");
        }
        sb.append("(input) (depth)\n");
        sb.append("let () = output_string out (print_k_binary(res))\n");
        sb.append("let () = try let subst = try_match res res (-1) in\n");
        sb.append("let code = get_exit_code subst in\n");
        sb.append("exit code\n");
        sb.append("with Stuck(res) -> output_string out (print_k_binary res); exit 112\n");
        return sb.toString();
    }

    private void matchPatternAndPrint(StringBuilder sb) {
        sb.append("let _ = (try print_subst_binary subst (try_match res res (-1)) with Stuck c -> output_string subst \"\\x00\\x00\\x00\\x00\")\n");
    }

    private void runAndPrint(int depth, StringBuilder sb) {
        sb.append("let res, steps = ");
        constructRun(sb, String.valueOf(depth));
        sb.append("\n");
        sb.append("let () = output_string out ((string_of_int steps) ^ \"\\n\" ^ print_k_binary(res))\n");
    }

    public void ocamlOpenFile(String name, String file, StringBuilder sb) {
        sb.append("let ").append(name).append(" = open_out_bin ").append(enquoteString(file)).append("\n");
    }

    /**
     * Generates a string containing ocaml code that, when executed, runs a particular program in the semantics.
     * Use this overload in order to precompute any configuration variables that are pure, leading to faster execution.
     * @param k The initial configuration to execute, minus the configuration
     *          variables present in the keys of that map
     * @param serializedVars A map from the names of configuration
     *                       variables to the result of encoding the value of the configuration variable using OCAML's
     *                       Marshal module.
     * @param topCellInitializer The klabel used to call the initializer of the top cell.
     * @param exitCode The pattern used to determine the integer exit code to return on the command line.
     * @param dumpExitCode A value that, if the integer matched by --exit-code is equal to this integer, indicates that the resulting configuration
     *                     from execution should be printed to the current working directory in a file named "config"
     * @return A program that can be compiled to rewrite the specified {@code k}.
     */
    public String ocamlCompile(KLabel topCellInitializer, Rule exitCode, Integer dumpExitCode) {
        StringBuilder sb = new StringBuilder();
        ocamlProgramHeader(sb, false);
        sb.append("let () = CONFIG.set_sys_argv ()\n");
        ocamlCompileSerializedInput(topCellInitializer, sb);
        return ocamlFinishCompile(exitCode, dumpExitCode, sb);
    }

    private String ocamlFinishCompile(Rule exitCode, Integer dumpExitCode, StringBuilder sb) {
        ocamlMatchPattern(exitCode, sb);
        sb.append("let _ = try let res, _ = ");
        constructRun(sb, "!CONFIG.depth");
        sb.append("in let subst = try_match res res (-1) in\n");
        sb.append("let code = get_exit_code subst in\n");
        if (dumpExitCode != null) {
            sb.append("(if code = ").append(dumpExitCode).append(" then\n");
            sb.append("(prerr_endline \"Execution failed (configuration dumped)\";\n");
            sb.append("let out = open_out !CONFIG.output_file in output_string out (print_k res))\n");
            sb.append("else ());\n");
        }
        sb.append("exit code\n");
        sb.append("with Stuck(res) -> (prerr_endline \"Execution failed (configuration dumped)\";\n");
        sb.append("let out = open_out !CONFIG.output_file in output_string out (print_k res);\n");
        sb.append("exit 139)\n");
        return sb.toString();
    }

    private void ocamlProgramHeader(StringBuilder sb, boolean forcePlugin) {
        if (forcePlugin) {
            sb.append("let () = Plugin.load Sys.argv.(1)");
        } else if (options.ocamlopt()) {
            sb.append("external load_plugin_path : unit -> string = \"load_plugin_path\"\n");
            sb.append("let () = Plugin.load (load_plugin_path ())");
        }
        sb.append("\nopen Prelude\nopen Constants\nopen Constants.K\nopen Run\nlet () = Sys.catch_break true\n");
        sb.append("let () = Gc.set { (Gc.get()) with Gc.minor_heap_size = 33554432 }");
    }

    private void ocamlCompileSerializedInput(KLabel topCellInitializer, StringBuilder sb) {
        // sb.append(enquoteString(ToBinary.apply(expandMacros.expand(k))));
        sb.append("external load_kore_term : unit -> string = \"load_kore_term\"\n");
        sb.append("external load_marshal_term : unit -> string = \"load_marshal_term\"\n");
        sb.append("let unserializedKMap = match Lexer.parse_k_binary_string (load_kore_term ()) with\n");
        sb.append("  [Map(SortMap, Lbl_Map_, m)] -> m\n");
        sb.append("| _ -> failwith \"kore_term is not of sort Map\"\n");
        sb.append("let serialized = (Marshal.from_string (load_marshal_term ()) 0 : Prelude.k)\n");
        sb.append("let serializedKMap = match serialized with\n");
        sb.append("  [Map(SortMap, Lbl_Map_, m)] -> m\n");
        sb.append("| _ -> failwith \"marshal_term is not of sort Map\"\n");
        sb.append("let completeMap = let conflict key val1 _ = Some val1 in\n" +
                  "    [(Map (SortMap, Lbl_Map_, KMap.union conflict unserializedKMap serializedKMap))]\n");
        sb.append("let input = (let module Def = (val Plugin.get ()) in Def.eval (KApply(");
        encodeStringToIdentifier(sb, topCellInitializer);
        sb.append(", [completeMap])) interned_bottom)\n");
    }

    private void ocamlTermInput(KRun.InitialConfiguration k, StringBuilder sb) {
        sb.append("let input = Lexer.parse_k_binary_string\n");
        K config = k.theConfig;
        k.theConfig = null;
        config = expandMacros.expand(config);
        byte[] binary = ToBinary.apply(config);
        config = null;
        String str = enquoteString(binary);
        binary = null;
        sb.append(str);
        str = null;
        sb.append("\n");
    }

    /**
     * Generates a string that, when compiled, writes a K term parsed from run.in into run.out using the
     * Marshal module.
     * @return
     */
    public String marshal() {
        StringBuilder sb = new StringBuilder();
        ocamlProgramHeader(sb, true);
        sb.append("let serialize, input, file = Makeconfig.marshal ()\n");
        sb.append("let str = if serialize then Marshal.to_string (input : Prelude.k) [] else print_k_binary input\n");
        sb.append("let () = output_string file str\n");
        return sb.toString();
    }

    public K preprocess(K k) {
        if (options.noExpandMacros) {
            return k;
        }
        return expandMacros.expand(k);
    }

    public String constants() {
        StringBuilder sb = new StringBuilder();
        sb.append("type sort = \n");
        Set<Sort> sorts = mutable(mainModule.definedSorts());
        sorts.add(Sorts.Bool());
        sorts.add(Sorts.Int());
        sorts.add(Sorts.String());
        sorts.add(Sorts.Float());
        sorts.add(Sorts.StringBuffer());
        sorts.add(Sorts.Bytes());
        for (Sort s : sorts) {
            sb.append("|");
            encodeStringToIdentifier(sb, s);
            sb.append("\n");
        }
        Set<KLabel> klabels = mutable(mainModule.definedKLabels());
        klabels.add(KLabel("#Bottom"));
        klabels.add(KLabel("littleEndianBytes"));
        klabels.add(KLabel("bigEndianBytes"));
        klabels.add(KLabel("signedBytes"));
        klabels.add(KLabel("unsignedBytes"));
        addOpaqueKLabels(klabels);
        sb.append("type klabel = \n");
        for (KLabel label : klabels) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append("\n");
        }
        sb.append("let print_sort(c: sort) : string = match c with \n");
        for (Sort s : sorts) {
            sb.append("|");
            encodeStringToIdentifier(sb, s);
            sb.append(" -> ");
            sb.append(enquoteString(s.toString()));
            sb.append("\n");
        }
        sb.append("let print_klabel(c: klabel) : string = match c with \n");
        for (KLabel label : klabels) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            sb.append(enquoteString(ToKast.apply(label)));
            sb.append("\n");
        }
        sb.append("let print_klabel_string(c: klabel) : string = match c with \n");
        for (KLabel label : klabels) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            sb.append(enquoteString(label.name()));
            sb.append("\n");
        }
        sb.append("let parse_sort(c: string) : sort = match c with \n");
        for (Sort s : sorts) {
            sb.append("|");
            sb.append(enquoteString(s.toString()));
            sb.append(" -> ");
            encodeStringToIdentifier(sb, s);
            sb.append("\n");
        }
        sb.append("| _ -> invalid_arg (\"parse_sort: \" ^ c)\n");
        sb.append("let parse_klabel(c: string) : klabel = match c with \n");
        for (KLabel label : klabels) {
            sb.append("|");
            sb.append(enquoteString(label.name()));
            sb.append(" -> ");
            encodeStringToIdentifier(sb, label);
            sb.append("\n");
        }
        sb.append("| _ -> invalid_arg (\"parse_klabel: \" ^ c)\n");
        sb.append("let collection_for (c: klabel) : klabel = match c with \n");
        for (Map.Entry<KLabel, KLabel> entry : collectionFor.entrySet()) {
            sb.append("|");
            encodeStringToIdentifier(sb, entry.getKey());
            sb.append(" -> ");
            encodeStringToIdentifier(sb, entry.getValue());
            sb.append("\n");
        }
        sb.append("| _ -> invalid_arg \"collection_for\"\n");
        sb.append("let unit_for (c: klabel) : klabel = match c with \n");
        for (KLabel label : collectionFor.values().stream().collect(Collectors.toSet())) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            encodeStringToIdentifier(sb, KLabel(mainModule.attributesFor().apply(label).get(Attribute.UNIT_KEY)));
            sb.append("\n");
        }
        sb.append("| _ -> invalid_arg \"unit_for\"\n");
        sb.append("let el_for (c: klabel) : klabel = match c with \n");
        for (KLabel label : collectionFor.values().stream().collect(Collectors.toSet())) {
            sb.append("|");
            encodeStringToIdentifier(sb, label);
            sb.append(" -> ");
            encodeStringToIdentifier(sb, KLabel(mainModule.attributesFor().apply(label).get("element")));
            sb.append("\n");
        }
        sb.append("| _ -> invalid_arg \"el_for\"\n");
        sb.append("let unit_for_array (c: sort) : klabel = match c with \n");
        Set<Sort> arraySorts = sorts.stream().filter(s -> mainModule.sortAttributesFor().get(s).getOrElse(() -> Att()).<String>getOptional("hook")
                .orElse(".").equals("ARRAY.Array")).collect(Collectors.toSet());
        for (Sort sort : arraySorts) {
            sb.append("|");
            encodeStringToIdentifier(sb, sort);
            sb.append(" -> ");
            encodeStringToIdentifier(sb, KLabel(mainModule.sortAttributesFor().apply(sort).get("unit")));
            sb.append("\n");
        }
        sb.append("| _ -> invalid_arg \"unit_for_array\"\n");
        sb.append("let el_for_array (c: sort) : klabel = match c with \n");
        for (Sort sort : arraySorts) {
            sb.append("|");
            encodeStringToIdentifier(sb, sort);
            sb.append(" -> ");
            encodeStringToIdentifier(sb, KLabel(mainModule.sortAttributesFor().apply(sort).get("element")));
            sb.append("\n");
        }
        sb.append("| _ -> invalid_arg \"el_for_array\"\n");
        sb.append("module Dynarray : sig\n" +
                "  type 'a t\n" +
                "  val make : int -> 'a -> 'a t\n" +
                "  val length : 'a t -> int\n" +
                "  val get : 'a t -> int -> 'a\n" +
                "  val set : 'a t -> int -> 'a -> unit\n" +
                "  val compare : ('a list -> 'a list -> int) -> 'a t -> 'a t -> int\n" +
                "  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a\n" +
                "  val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b\n" +
                "  val iteri : (int -> 'a -> unit) -> 'a t -> unit\n" +
                "end = struct\n" +
                "  type 'a t = { size: int;" +
                "                mutable arr: 'a array;" +
                "                default: 'a }\n" +
                "  let make size default = { size=size; arr=Array.make (min size 10) default; default=default}\n" +
                "  let length arr = arr.size\n" +
                "  let get arr idx = if idx >= Array.length arr.arr && idx < arr.size then arr.default else Array.get arr.arr idx\n" +
                "  let calc_size arr at_least = let double = Array.length arr.arr * 2 in\n" +
                "    let at_most = if double > arr.size then arr.size else double in\n" +
                "    if at_least > at_most then at_least else at_most\n" +
                "  let upgrade_size arr size = let old = arr.arr in" +
                "    arr.arr <- Array.make size arr.default;" +
                "    Array.blit old 0 arr.arr 0 (Array.length old)\n" +
                "  let set arr idx value= if idx >= Array.length arr.arr && idx < arr.size then upgrade_size arr (calc_size arr (idx + 1));\n" +
                "    Array.set arr.arr idx value\n" +
                "  let compare_arr f a b = let smaller,larger = if Array.length a.arr < Array.length b.arr then a,b else b,a in\n" +
                "  upgrade_size smaller (Array.length larger.arr);\n" +
                "  f (Array.to_list a.arr) (Array.to_list b.arr)\n" +
                "  let compare f a b = let v = Pervasives.compare a.size b.size in if v = 0 then compare_arr f a b else v\n" +
                "  let fold_left f init arr = snd (Array.fold_left (fun (i,x) a -> if i > 0 then (i - 1, f x a) else (0,x))  (arr.size,init) arr.arr)\n" +
                "  let fold_right f arr init = snd (Array.fold_right (fun a (i,x) -> if i > 0 then (i - 1, x) else (0, f a x)) arr.arr (Array.length arr.arr - arr.size, init))\n" +
                "  let iteri f arr = Array.iteri (fun i a -> if i < arr.size then f i a else ()) arr.arr\n" +
                "end\n");
        sb.append("\n\nmodule type S =\n");
        sb.append("sig\n");
        sb.append("  type m\n");
        sb.append("  type s\n");
        sb.append("  type t = kitem list\n");
        Set<Long> arities = printKType(klabels, sb);
        sb.append("  val compare : t -> t -> int\n" +
                "  val compare_kitem : kitem -> kitem -> int\n" +
                "  val compare_klist : t list -> t list -> int\n" +
                "  val equal_k : t -> t -> bool\n" +
                "  val hash_k : t -> int\n" +
                "  val hash_k_param : int -> t -> int\n" +
                "end\n");
        sb.append("module rec K : (S with type m = K.t Map.Make(K).t and type s = Set.Make(K).t)  =\n" +
                "struct\n" +
                "  module KMap = Map.Make(K)\n" +
                "  module KSet = Set.Make(K)\n" +
                "  type m = K.t KMap.t\n" +
                "  and s = KSet.t\n" +
                "  and t = kitem list\n");
        printKType(klabels, sb);
        sb.append("let rec hash_k c = match c with\n" +
                "    | [] -> 1\n" +
                "    | hd :: tl -> (hash_k tl) * 31 + hash_kitem hd\n" +
                "  and hash_kitem c = match c with\n");
        for (long arity : arities) {
            sb.append("    | KApply").append(arity).append("(lbl");
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i);
            }
            sb.append(") -> ");
            int i;
            for (i = 0; i < arity; i++) {
                sb.append("(");
            }
            sb.append("(Hashtbl.hash lbl)");
            for (i = 0; i < arity; i++) {
                sb.append(") * 37 + hash_k k").append(i);
            }
            sb.append("\n");
        }
        sb.append("    | KToken(s, st) -> Hashtbl.hash s * 41 + Hashtbl.hash st\n" +
                "    | InjectedKLabel kl -> Hashtbl.hash kl\n" +
                "    | Map(_,k,m) -> Hashtbl.hash k * 43 + KMap.fold (fun k v accum -> accum + (hash_k k lxor hash_k v)) m 0\n" +
                "    | List(_,k,l) -> Hashtbl.hash k * 47 + hash_klist l\n" +
                "    | Set(_,k,s) -> Hashtbl.hash k * 53 + KSet.fold (fun k accum -> accum + hash_k k) s 0\n" +
                "    | Array(k,_,l) -> Hashtbl.hash k * 61 + (Dynarray.length l)\n" +
                "    | Int i -> Z.hash i\n" +
                "    | Float (f,_,_) -> Hashtbl.hash (Gmp.FR.to_float f)\n" +
                "    | String s -> Hashtbl.hash s\n" +
                "    | StringBuffer s -> Hashtbl.hash (Buffer.contents s)\n" +
                "    | Bytes b -> Hashtbl.hash b\n" +
                "    | Bool b -> Hashtbl.hash b\n" +
                "    | Bottom -> 1\n" +
                "    | ThreadLocal -> 2\n" +
                "    | Thread(k1,k2,k3,k4) -> ((((Hashtbl.hash Lbl'Hash'Thread) * 37 + hash_k k1) * 37 + hash_k k2) * 37 + hash_k k3) * 36 + hash_k k4\n" +
                "  and hash_klist c = match c with\n" +
                "    | [] -> 1\n" +
                "    | hd :: tl -> (hash_klist tl) * 59 + hash_k hd\n");

        sb.append("let rec hash_k_param_fld ((l,max) as lmax) = function \n" +
                "  | [] -> lmax\n" +
                "  | h::t -> if max < 0 then lmax else hash_k_param_fld (h::l,max-1) t\n" +
                "\n" +
                "let hash_k_param_add_kitem k max =\n" +
                "  hash_k_param_fld max k\n" +
                "\n" +
                "let rec qfld l1 h max = match l1 with \n" +
                "  | [] -> let (l2,max) = max in if l2 = [] then h else qfld l2 h ([],max)\n" +
                "  | ki :: kq -> match ki with \n");
        for (long arity : arities) {
            sb.append("    | KApply").append(arity).append("(lbl");
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i);
            }
            sb.append(") -> \n");
            sb.append("        qfld kq (31*h + Hashtbl.hash lbl) (\n");
            for (int i = 0; i < arity; i++) {
                sb.append("        hash_k_param_add_kitem k").append(i).append(" (\n");
            }
            sb.append("        max)");
            for (int i = 0; i < arity; i++) {
                sb.append(')');
            }
            sb.append('\n');
        }
        sb.append("    | KToken(s, st) ->\n" +
                "        qfld kq (31*h + Hashtbl.hash s * 41 + Hashtbl.hash st) (\n" +
                "        max)\n" +
                "    | InjectedKLabel lbl ->\n" +
                "        qfld kq (31*h + Hashtbl.hash lbl) (\n" +
                "        max)\n" +
                "    | Map(_,lbl,m) -> \n" +
                "        qfld kq (31*h + 43 * Hashtbl.hash lbl) (\n" +
                "        KMap.fold (fun k v max -> hash_k_param_add_kitem v (hash_k_param_add_kitem k max)) m max)\n" +
                "    | List(_,lbl,l) ->\n" +
                "        qfld kq (31*h + 47 * Hashtbl.hash lbl) (\n" +
                "        List.fold_left (fun max k -> hash_k_param_add_kitem k max) max l)\n" +
                "    | Set(_,lbl,s) ->\n" +
                "        qfld kq (31*h + 53 * Hashtbl.hash lbl) (\n" +
                "        KSet.fold (fun k max -> hash_k_param_add_kitem k max) s max)\n" +
                "    | Array(lbl,_,l) -> \n" +
                "        qfld kq (31*h + 61 * Hashtbl.hash lbl + Dynarray.length l) (\n" +
                "        max)\n" +
                "    | Int i -> qfld kq (31*h + Z.hash i) (\n" +
                "        max)\n" +
                "    | Float (f,_,_) -> qfld kq (31*h + Hashtbl.hash (Gmp.FR.to_float f)) (\n" +
                "        max)\n" +
                "    | String s -> qfld kq (31*h + Hashtbl.hash s) (\n" +
                "        max)\n" +
                "    | Bytes b -> qfld kq (31*h + Hashtbl.hash b) (\n" +
                "        max)\n" +
                "    | StringBuffer s -> qfld kq (31*h + Hashtbl.hash (Buffer.contents s)) (\n" +
                "        max)\n" +
                "    | Bool b -> qfld kq (31*h + Hashtbl.hash b) (\n" +
                "        max)\n" +
                "    | Bottom -> qfld kq (31*h + 1) (\n" +
                "        max)\n" +
                "    | ThreadLocal -> qfld kq (31*h + 2) (\n" +
                "        max)\n" +
                "    | Thread(k1,k2,k3,k4) -> qfld kq (31*h + Hashtbl.hash Lbl'Hash'Thread) (hash_k_param_add_kitem k1 (hash_k_param_add_kitem k2 (hash_k_param_add_kitem k3 (hash_k_param_add_kitem k4 max))))\n" +
                "\n");
        sb.append("let hash_k_param max k = \n" +
                "    qfld [] 0 (hash_k_param_add_kitem k ([],max))\n" +
                "\n");

        sb.append("  let rec equal_k c1 c2 = if c1 == c2 then true else match (c1, c2) with\n" +
                "    | [], [] -> true\n" +
                "    | (hd1 :: tl1), (hd2 :: tl2) -> equal_kitem hd1 hd2 && equal_k tl1 tl2\n" +
                "    | _ -> false\n" +
                "  and equal_kitem c1 c2 = if c1 == c2 then true else match (c1, c2) with\n");
        for(long arity : arities) {
            sb.append("    | KApply").append(arity).append("(lbl1");
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i).append("_1");
            }
            sb.append("),KApply").append(arity).append("(lbl2");
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i).append("_2");
            }
            sb.append(") -> lbl1 = lbl2");
            int i;
            for (i = 0; i < arity; i++) {
                sb.append(" && equal_k k").append(i).append("_1 k").append(i).append("_2");
            }
            sb.append("\n");
        }
        sb.append("    | (KToken(s1, st1)), (KToken(s2, st2)) -> s1 = s2 && st1 = st2\n" +
                "    | (InjectedKLabel kl1), (InjectedKLabel kl2) -> kl1 = kl2\n" +
                "    | (Map (_,k1,m1)), (Map (_,k2,m2)) -> k1 = k2 && KMap.cardinal m1 = KMap.cardinal m2 && (KMap.equal) (equal_k) m1 m2\n" +
                "    | (List (_,k1,l1)), (List (_,k2,l2)) -> k1 = k2 && equal_klist l1 l2\n" +
                "    | (Set (_,k1,s1)), (Set (_,k2,s2)) -> k1 = k2 && KSet.cardinal s1 = KSet.cardinal s2 && (KSet.equal) s1 s2\n" +
                "    | (Array (s1,k1,l1)), (Array (s2,k2,l2)) -> s1 = s2 && equal_k k1 k2 && l1 == l2\n" +
                "    | (Int i1), (Int i2) -> Z.equal i1 i2\n" +
                "    | (Float (f1,e1,p1)), (Float (f2,e2,p2)) -> e1 = e2 && p1 = p2 && Gmp.FR.compare f1 f2 = 0\n" +
                "    | (String s1), (String s2) -> s1 = s2\n" +
                "    | (Bytes b1), (Bytes b2) -> b1 == b2\n" +
                "    | (StringBuffer s1), (StringBuffer s2) -> s1 == s2\n" +
                "    | (Bool b1), (Bool b2) -> b1 = b2\n" +
                "    | Bottom, Bottom -> true\n" +
                "    | _ -> false\n" +
                "  and equal_klist c1 c2 = if c1 == c2 then true else match (c1, c2) with\n" +
                "    | [], [] -> true\n" +
                "    | (hd1 :: tl1), (hd2 :: tl2) -> equal_k hd1 hd2 && equal_klist tl1 tl2\n" +
                "    | _ -> false\n");
        sb.append("  let rec compare c1 c2 = if c1 == c2 then 0 else match (c1, c2) with\n" +
                "    | [], [] -> 0\n" +
                "    | (hd1 :: tl1), (hd2 :: tl2) -> let v = compare_kitem hd1 hd2 in if v = 0 then compare tl1 tl2 else v\n" +
                "    | (_ :: _), _ -> -1\n" +
                "    | _ -> 1\n" +
                "  and compare_kitem c1 c2 = if c1 == c2 then 0 else match (c1, c2) with\n");
        for(long arity : arities) {
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
                "    | (Array (s1,k1,l1)), (Array (s2,k2,l2)) -> let v = Pervasives.compare s1 s2 in if v = 0 then let v = compare k1 k2 in if v = 0 then Dynarray.compare compare_klist l1 l2 else v else v\n" +
                "    | (Int i1), (Int i2) -> Z.compare i1 i2\n" +
                "    | (Float (f1,e1,p1)), (Float (f2,e2,p2)) -> let v = e2 - e1 in if v = 0 then let v2 = p2 - p1 in if v2 = 0 then Gmp.FR.compare f1 f2 else v2 else v\n" +
                "    | (String s1), (String s2) -> Pervasives.compare s1 s2\n" +
                "    | (Bytes b1), (Bytes b2) -> Pervasives.compare b1 b2\n" +
                "    | (StringBuffer s1), (StringBuffer s2) -> Pervasives.compare (Buffer.contents s1) (Buffer.contents s2)\n" +
                "    | (Bool b1), (Bool b2) -> if b1 = b2 then 0 else if b1 then -1 else 1\n" +
                "    | Bottom, Bottom -> 0\n" +
                "    | ThreadLocal, ThreadLocal -> 0\n" +
                "    | Thread (k11, k12, k13, k14), Thread (k21, k22, k23, k24) -> let v = compare k11 k21 in if v = 0 then let v = compare k12 k22 in if v = 0 then let v = compare k13 k23 in if v = 0 then compare k14 k24 else v else v else v\n");
        for(long i : arities) {
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
                "    | Array(_), _ -> -1\n" +
                "    | _, Array(_) -> 1\n" +
                "    | Int(_), _ -> -1\n" +
                "    | _, Int(_) -> 1\n" +
                "    | Float(_), _ -> -1\n" +
                "    | _, Float(_) -> 1\n" +
                "    | String(_), _ -> -1\n" +
                "    | _, String(_) -> 1\n" +
                "    | Bytes(_), _ -> -1\n" +
                "    | _, Bytes(_) -> 1\n" +
                "    | StringBuffer(_), _ -> -1\n" +
                "    | _, StringBuffer(_) -> 1\n" +
                "    | Bool(_), _ -> -1\n" +
                "    | _, Bool(_) -> 1\n" +
                "    | Bottom, _ -> -1\n" +
                "    | _, Bottom -> 1\n" +
                "    | ThreadLocal, _ -> -1\n" +
                "    | _, ThreadLocal -> 1\n" +
                "  and compare_klist c1 c2 = match (c1, c2) with\n" +
                "    | [], [] -> 0\n" +
                "    | (hd1 :: tl1), (hd2 :: tl2) -> let v = compare hd1 hd2 in if v = 0 then compare_klist tl1 tl2 else v\n" +
                "    | (_ :: _), _ -> -1\n" +
                "    | _ -> 1\n" +
                "end\n");
        sb.append("type normal_kitem = KApply of klabel * K.t list\n");
        sb.append("                  | KItem of K.kitem\n");
        sb.append("open K\n");
        sb.append("let normalize (k: kitem) : normal_kitem = match k with \n");
        for (long arity : arities) {
            sb.append("  | KApply").append(arity).append("(lbl");
            for (int i = 0; i < arity; i++) {
                sb.append(",k").append(i);
            }
            sb.append(") -> KApply (lbl, [");
            String conn = "";
            for (int i = 0; i < arity; i++) {
                sb.append(conn);
                sb.append("k").append(i);
                conn = "; ";
            }
            sb.append("])\n");
        }
        sb.append("| v -> KItem v\n");
        sb.append("let denormalize (k: normal_kitem) : kitem = match k with \n");
        for (long arity : arities) {
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
        sb.append("| KItem v -> v\n| KApply (_, _) -> invalid_arg \"denormalize\"\ntype k = K.t\n");
        for (long arity : arities) {
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
            sb.append(")\n| _ -> invalid_arg \"normalize").append(arity).append("\"\n");
        }

        Set<String> integerConstants = new HashSet<>();
        for (Rule r : iterable(mainModule.rules())) {
            integers(r.body(), integerConstants);
            integers(r.requires(), integerConstants);
        }
        for (String i : integerConstants) {
            sb.append("let ");
            encodeStringToIntConst(sb, i);
            sb.append(" = lazy (Int (Z.of_string \"").append(i).append("\"))\n");
        }
        forEachKLabel(t -> {
            if (t._2() == 0) {
                sb.append("let const");
                encodeStringToAlphanumeric(sb, t._1().name());
                sb.append(" = KApply0(");
                encodeStringToIdentifier(sb, t._1());
                sb.append(")\n");
            }
        });

        sb.append("let val_for (c: klabel) (k : k) (v : k) : normal_kitem = match c with\n");
        for (KLabel ctor : filteredMapConstructors) {
            sb.append('|');
            encodeStringToIdentifier(sb, ctor);
            sb.append(" -> (match v with [KApply2(_, k, v)] -> KApply((el_for c), [k;v]) | _ -> invalid_arg \"val_for\")\n");
        }
        sb.append("|_ -> KApply((el_for c), [k;v])\n");
        return sb.toString();
    }

    private void addOpaqueKLabels(Set<KLabel> klabels) {
        if (options.klabels == null)
            return;
        File definitionFile = files.resolveWorkingDirectory(options.klabels).getAbsoluteFile();
        List<File> lookupDirectories = kompileOptions.outerParsing.includes.stream().map(files::resolveWorkingDirectory).collect(Collectors.toList());
        lookupDirectories.add(Kompile.BUILTIN_DIRECTORY);
        java.util.Set<Module> mods = new ParserUtils(files::resolveWorkingDirectory, kem, globalOptions).loadModules(
                new HashSet<>(),
                new Context(),
                "require " + StringUtil.enquoteCString(definitionFile.getPath()),
                Source.apply(definitionFile.getAbsolutePath()),
                definitionFile.getParentFile(),
                lookupDirectories,
                new HashSet<>(), false);
        mods.stream().forEach(m -> klabels.addAll(mutable(m.definedKLabels())));
    }

    private void integers(K term, Set<String> accum) {
        new VisitK() {
            @Override
            public void apply(KToken k) {
                if (k.sort().equals(Sorts.Int())) {
                    accum.add(k.s());
                }
            }
        }.apply(term);
    }

    private Set<Long> printKType(Set<KLabel> klabels, StringBuilder sb) {
        sb.append("  and kitem = KToken of sort * string\n");
        sb.append("            | InjectedKLabel of klabel\n");
        sb.append("            | Map of sort * klabel * m\n");
        sb.append("            | List of sort * klabel * t list\n");
        sb.append("            | Set of sort * klabel * s\n");
        sb.append("            | Array of sort * t * t Dynarray.t\n");
        sb.append("            | Int of Z.t\n");
        sb.append("            | Float of Gmp.FR.t * int * int\n");
        sb.append("            | String of string\n");
        sb.append("            | Bytes of bytes\n");
        sb.append("            | StringBuffer of Buffer.t\n");
        sb.append("            | Bool of bool\n");
        sb.append("            | ThreadLocal\n");
        sb.append("            | Thread of t * t * t * t\n");
        sb.append("            | Bottom\n");
        Set<Long> arities = new HashSet<>();
        forEachKLabel(t -> arities.add(t._2()));
        for (long arity : arities) {
            sb.append("            | KApply").append(arity).append(" of klabel");
            for (int i = 0; i < arity; i++) {
                sb.append(" * t");
            }
            sb.append("\n");
        }
        return arities;
    }

    private void forEachKLabel(Consumer<Tuple2<KLabel, Long>> action) {
        for (KLabel label : iterable(mainModule.definedKLabels())) {
            if (ConvertDataStructureToLookup.isLookupKLabel(label) || label.name().equals("#KToken"))
                continue;
            stream(mainModule.productionsFor().apply(label)).map(p -> Tuple2.apply(p.klabel().get(), stream(p.items()).filter(pi -> pi instanceof NonTerminal).count())).distinct().forEach(action);
        }
    }

    private static <V> Set<V> ancestors(
            Collection<? extends V> startNodes, DirectedGraph<V, ?> graph)
    {
        Queue<V> queue = new LinkedList<V>();
        Set<V> visited = new LinkedHashSet<V>();
        queue.addAll(startNodes);
        visited.addAll(startNodes);
        while(!queue.isEmpty())
        {
            V v = queue.poll();
            Collection<V> neighbors = graph.getPredecessors(v);
            for (V n : neighbors)
            {
                if (!visited.contains(n))
                {
                    queue.offer(n);
                    visited.add(n);
                }
            }
        }
        return visited;
    }

    private Set<KLabel> constants;
    private Map<KLabel, String> realStepFunctions = new HashMap<>();

    public String definition() {
        StringBuilder sb = new StringBuilder();
        sb.append("open Prelude\nopen Constants\nopen Constants.K\nopen Hooks\nmodule Def = struct\n");
        SetMultimap<KLabel, Rule> functionRules = HashMultimap.create();
        ListMultimap<KLabel, Rule> anywhereRules = ArrayListMultimap.create();
        anywhereKLabels = new HashSet<>();
        stream(mainModule.rules()).filter(r -> !ExpandMacros.isMacro(r)).forEach(r -> {
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
        });
        functions = new HashSet<>(functionRules.keySet());
        for (Production p : iterable(mainModule.productions())) {
            if (p.att().contains(Attribute.FUNCTION_KEY)) {
                functions.add(p.klabel().get());
            }
        }

        SetMultimap<KLabel, Rule> rules = HashMultimap.create(functionRules);
        klabelsForEachPredicate = new HashMap<>();
        for (KLabel functionLabel : rules.keySet()) {
            if (mainModule.attributesFor().get(functionLabel).getOrElse(() -> Att()).contains("klabelPredicate")) {
                klabelsForEachPredicate.put(functionLabel.name(), computeKLabelsForPredicate(functionRules.get(functionLabel)));
            }
        }
        rules.putAll(anywhereRules);
        List<List<KLabel>> functionOrder = sortFunctions(rules);

        //compute fixed point. The only hook that actually requires this argument is KREFLECTION.fresh, so we will automatically
        //add the real definition of this function before we declare any function that requires it.
        sb.append("let freshFunction (sort: string) (config: k) (counter: Z.t) : k = interned_bottom\n");
        Set<KLabel> impurities = functions.stream().filter(lbl -> mainModule.attributesFor().apply(lbl).contains(Attribute.IMPURE_KEY)).collect(Collectors.toSet());
        impurities.addAll(ancestors(impurities, dependencies));
        constants = functions.stream().filter(lbl -> !impurities.contains(lbl) && stream(mainModule.productionsFor().apply(lbl)).filter(p -> p.arity() == 0).findAny().isPresent()).collect(Collectors.toSet());


        for (List<KLabel> component : functionOrder) {
            String conn;
            final boolean isLetRec;
            if (component.size() == 1) {
                MutableBoolean isRecursive = new MutableBoolean(false);
                for (Rule r : rules.get(component.get(0))) {
                    class ComputeRecursion extends VisitK {
                        @Override
                        public void apply(KApply k) {
                            if (k.klabel().equals(component.get(0))) {
                                isRecursive.setTrue();
                            }
                            super.apply(k);
                        }
                    }
                    new ComputeRecursion().apply(RewriteToTop.toRight(r.body()));
                    new ComputeRecursion().apply(r.requires());
                    if (hasLookups(r)) {
                        isRecursive.setTrue();
                    }
                }
                if (isRecursive.getValue()) {
                    conn = "let rec ";
                    isLetRec = true;
                } else {
                    conn = "let ";
                    isLetRec = false;
                }
            } else {
                conn = "let rec ";
                isLetRec = true;
            }
            for (KLabel functionLabel : component) {
                String hook = mainModule.attributesFor().get(functionLabel).getOrElse(() -> Att()).<String>getOptional(Attribute.HOOK_KEY).orElse(".");
                if (hook.equals("KREFLECTION.fresh")) {
                    sb.append(conn).append("freshFunction (sort: string) (config: k) (counter: Z.t) : k = match sort with \n");
                    for (Sort sort : iterable(mainModule.freshFunctionFor().keys())) {
                        sb.append("| \"").append(sort.toString()).append("\" -> (");
                        KLabel freshFunction = mainModule.freshFunctionFor().apply(sort);
                        encodeStringToFunction(sb, freshFunction);
                        sb.append(" ([Int counter]) config (-1))\n");
                    }
                    sb.append("| _ -> invalid_arg (\"Cannot find fresh function for sort \" ^ sort)");
                    if (isLetRec) {
                        conn = "and ";
                    }
                }
                if (functions.contains(functionLabel)) {
                    sb.append(conn);
                    String functionName;
                    if (mainModule.attributesFor().apply(functionLabel).contains("memo")) {
                        functionName = encodeStringToMemoFunction(sb, functionLabel);
                    } else {
                        functionName = encodeStringToFunction(sb, functionLabel);
                    }
                    int arity = getArity(functionLabel);
                    printFunctionParams(sb, arity);
                    sb.append(" (config: k) (guard: int) : k = let lbl = \n");
                    encodeStringToIdentifier(sb, functionLabel);
                    sb.append(" and sort = \n");
                    encodeStringToIdentifier(sb, mainModule.sortFor().apply(functionLabel));
                    sb.append(" in ");
                    sb.append("match c with \n");
                    String namespace = hook.substring(0, hook.indexOf('.'));
                    String function = hook.substring(namespace.length() + 1);
                    if (hookNamespaces.contains(namespace) || kompileOptions.hookNamespaces.contains(namespace)) {
                        sb.append("| _ -> try ").append(namespace).append(".hook_").append(function).append(" c lbl sort config freshFunction");
                        if (mainModule.attributesFor().apply(functionLabel).contains("canTakeSteps")) {
                            sb.append(" eval");
                        }
                        sb.append("\nwith Not_implemented -> match c with \n");
                    } else if (!hook.equals(".")) {
                        kem.registerCompilerWarning("missing entry for hook " + hook);
                    }

                    if (mainModule.attributesFor().apply(functionLabel).contains(Attribute.PREDICATE_KEY, Sort.class)) {
                        Sort predicateSort = (mainModule.attributesFor().apply(functionLabel).get(Attribute.PREDICATE_KEY, Sort.class));
                        stream(mainModule.definedSorts()).filter(s -> mainModule.subsorts().greaterThanEq(predicateSort, s)).distinct()
                                .filter(sort -> mainModule.sortAttributesFor().contains(sort)).forEach(sort -> {
                            String sortHook = mainModule.sortAttributesFor().apply(sort).<String>getOptional("hook").orElse("");
                            if (predicateRules.containsKey(sortHook)) {
                                sb.append("| ");
                                sb.append(predicateRules.get(sortHook).apply(sort));
                                sb.append("\n");
                            }
                        });
                    }

                    convertFunction(functionRules.get(functionLabel).stream().sorted(this::sortFunctionRules).collect(Collectors.toList()),
                            sb, functionName, RuleType.FUNCTION);
                    sb.append("| _ -> raise (Stuck [denormalize (KApply(lbl, (denormalize").append(arity).append(" c)))])\n");
                    if (constants.contains(functionLabel)) {
                        sb.append(conn.equals("let rec ") ? "and " : conn);
                        sb.append("const");
                        encodeStringToAlphanumeric(sb, functionLabel.name());
                        sb.append(" : k Lazy.t = lazy (");
                        encodeStringToFunction(sb, functionLabel);
                        sb.append(" () interned_bottom (-1))\n");
                    } else if (mainModule.attributesFor().apply(functionLabel).contains("memo")) {
                        encodeMemoizationOfFunction(sb, conn, functionLabel, functionName, arity);
                    }
                    conn = "and ";
                } else if (anywhereKLabels.contains(functionLabel)) {
                    sb.append(conn);
                    String functionName = encodeStringToFunction(sb, functionLabel);
                    int arity = getArity(functionLabel);
                    printFunctionParams(sb, arity);
                    sb.append(" (config: k) (guard: int) : k = let lbl = \n");
                    encodeStringToIdentifier(sb, functionLabel);
                    sb.append(" in match c with \n");
                    convertFunction(anywhereRules.get(functionLabel), sb, functionName, RuleType.ANYWHERE);
                    sb.append("| ");
                    for (int i = 0; i < arity; i++) {
                        sb.append("k").append(i);
                        if (i != arity - 1) {
                            sb.append(",");
                        }
                    }
                    if (arity == 0)
                        sb.append("()");
                    sb.append(" -> [KApply").append(arity).append("(lbl");
                    for (int i = 0; i < arity; i++) {
                        sb.append(", k").append(i);
                    }
                    sb.append(")]\n");
                    conn = "and ";
                } else if (functionLabel.name().isEmpty()) {
                    //placeholder for eval function;
                    sb.append(conn);
                    sb.append("eval (c: normal_kitem) (config: k) : k = match c with KApply(lbl, kl) -> (match lbl with \n");
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
                }
            }
        }
        List<Rule> unsortedRules = stream(mainModule.rules()).collect(Collectors.toList());
        if (options.reverse) {
            Collections.reverse(unsortedRules);
        }
        List<Rule> sortedRules = unsortedRules.stream()
                .sorted(this::sortRules)
                .filter(r -> !functionRules.values().contains(r) && !ExpandMacros.isMacro(r) && !r.att().contains(Attribute.ANYWHERE_KEY))
                .collect(Collectors.toList());
        sb.append("let rec get_next_op_from_exp(c: kitem) : (k -> k * (step_function)) = ");
        Set<KLabel> allStepFunctions = Sets.difference(mutable(mainModule.definedKLabels()), functions);
        Map<Optional<KLabel>, List<Rule>> groupedByStepFunction = sortedRules.stream().collect(
                Collectors.groupingBy(r -> getNextOperation(RewriteToTop.toLeft(r.body()), false)));
        if (options.optimizeStep()) {
            sb.append("match c with KApply1(_,hd :: tl) -> (\n");
            sb.append("match (normalize hd) with KApply(lbl,_) -> (match lbl with \n");
            for (KLabel lbl : allStepFunctions) {
                sb.append("| ");
                encodeStringToIdentifier(sb, lbl);
                sb.append(" -> step");
                if (groupedByStepFunction.containsKey(Optional.of(lbl))) {
                    String textLbl = encodeStringToIdentifier(lbl);
                    sb.append(textLbl);
                    realStepFunctions.put(lbl, "step" + textLbl);
                } else {
                    sb.append("None");
                    realStepFunctions.put(lbl, "stepNone");
                }
                sb.append("\n");
            }
            sb.append("| _ -> stepNone) | _ -> stepNone) | _ -> stepNone\n");
        } else {
            sb.append("step\n");
        }
        int ruleNum = writeStepFunction(sb, sortedRules, "step", 0);
        for (KLabel lbl : groupedByStepFunction.keySet().stream().filter(Optional::isPresent).map(Optional::get).collect(Collectors.toSet())) {
            List<Rule> rulesForStepFunc = ListUtils.union(
                    groupedByStepFunction.getOrDefault(Optional.of(lbl), Collections.emptyList()),
                    filterNoneRulesByVariableType(lbl, groupedByStepFunction.getOrDefault(Optional.<KLabel>empty(), Collections.emptyList()), functionRules));
            Collections.sort(rulesForStepFunc, this::sortRules);
            ruleNum = writeStepFunction(sb, rulesForStepFunc, "step" + encodeStringToIdentifier(lbl), ruleNum);
        }
        if (options.optimizeStep()) {
            ruleNum = writeStepFunction(sb, groupedByStepFunction.getOrDefault(Optional.<KLabel>empty(), Collections.emptyList()), "stepNone", ruleNum);
        }

        if (makeStuck != null) {
            sb.append("let set_stuck (c: k) (config: k) (guard: int) : k * step_function = match c with \n");
            convertFunction(Collections.singletonList(makeStuck), sb, "step", RuleType.REGULAR);
            sb.append("| _ -> (c, (StepFunc step))\n");
            sb.append("let make_stuck (config: k) : k =\n");
            sb.append("  fst (set_stuck config config (-1))\n");
        } else {
            sb.append("let make_stuck (config: k) : k = config\n");
        }

        if (makeUnstuck != null) {
            sb.append("let set_unstuck (c: k) (config: k) (guard: int) : k * step_function = match c with \n");
            convertFunction(Collections.singletonList(makeUnstuck), sb, "step", RuleType.REGULAR);
            sb.append("| _ -> (c, (StepFunc step))\n");
            sb.append("let make_unstuck (config: k) : k =\n");
            sb.append("  fst (set_unstuck config config (-1))\n");
        } else {
            sb.append("let make_unstuck (config: k) : k = config\n");
        }

        if (matchThreadSet == null) {
            // no threads
            sb.append("let get_thread_set (config: k) : k = [Map(SortMap,Lbl_Map_,KMap.empty)]\n");
            sb.append("let set_thread_set (config: k) (set: k) : k = config\n");
        } else {
            if (hasLookups(matchThreadSet)) {
                sb.append("let rec ");
            } else {
                sb.append("let ");
            }
            sb.append("match_thread_set (c: k) (config: k) (guard: int) : k Subst.t = match c with \n");
            convertFunction(Collections.singletonList(matchThreadSet), sb, "match_thread_set", RuleType.PATTERN);
            sb.append("| _ -> failwith \"match_thread_set\"\n");
            sb.append("let get_thread_set (config: k) : k =\n");
            sb.append("  let subst = match_thread_set config config (-1) in\n");
            sb.append("  Subst.find \"Threads\" subst\n");
            if (hasLookups(rewriteThreadSet)) {
                sb.append("let rec ");
            } else {
                sb.append("let ");
            }
            sb.append("rewrite_thread_set (c: k) (config: k) (guard: int) (new_threads: k) : k = match c with \n");
            {
                Rule r = rewriteThreadSet;
                convertComment(r, sb);
                sb.append("| ");
                K left = RewriteToTop.toLeft(r.body());
                K requires = r.requires();
                VarInfo vars = new VarInfo();
                vars.vars.put(KVariable("NewThreads"), "new_threads");
                convertLHS(sb, RuleType.REGULAR, left, vars);
                String result = convert(vars);
                String suffix = "";
                if (!requires.equals(KSequence(BooleanUtils.TRUE)) || !result.equals("true")) {
                    suffix = convertSideCondition(sb, requires, vars, Collections.emptyList(), true, RuleType.REGULAR, ruleNum);
                }
                sb.append(" -> ");
                convertRHS(sb, RuleType.REGULAR, r, vars, suffix, ruleNum, "", false);
            }
            sb.append("| _ -> failwith \"rewrite_thread_set\"\n");
            sb.append("let set_thread_set (config: k) (set: k) : k =\n");
            sb.append("  rewrite_thread_set config config (-1) set\n");
        }
        sb.append("end\nlet () = Plugin.the_definition := Some (module Def)\n");
        return sb.toString();
    }

    private int sortRules(Rule r1, Rule r2) {
        return ComparisonChain.start()
                .compareTrueFirst(r1.att().contains("structural"), r2.att().contains("structural"))
                .compareFalseFirst(r1.att().contains("owise"), r2.att().contains("owise"))
                .compareFalseFirst(indexesPoorly(r1), indexesPoorly(r2))
                .result();
    }

    private List<KLabel> computeKLabelsForPredicate(Set<Rule> rules) {
        List<KLabel> labels = new ArrayList<>();
        for (Rule r : rules) {
            K body = r.body();
            K lhs = RewriteToTop.toLeft(body);
            K rhs = RewriteToTop.toRight(body);
            if (rhs.equals(KSequence(BooleanUtils.FALSE)) && r.att().contains("owise")) {
                continue;
            }
            if (!rhs.equals(KSequence(BooleanUtils.TRUE))) {
                throw KEMException.compilerError("Unexpected form for klabel predicate rule, expected predicate(_) => false [owise] or predicate(#klabel(`klabel`)) => true.", r);
            }
            if (!(lhs instanceof KSequence)) {
                throw KEMException.compilerError("Unexpected form for klabel predicate rule, expected predicate(_) => false [owise] or predicate(#klabel(`klabel`)) => true.", r);
            }
            KSequence kseq = (KSequence) lhs;
            if (kseq.items().size() != 1 || !(kseq.items().get(0) instanceof KApply)) {
                throw KEMException.compilerError("Unexpected form for klabel predicate rule, expected predicate(_) => false [owise] or predicate(#klabel(`klabel`)) => true.", r);
            }
            KApply function = (KApply)kseq.items().get(0);
            if (function.items().size() != 1 || !(function.items().get(0) instanceof KSequence)) {
                throw KEMException.compilerError("Unexpected form for klabel predicate rule, expected predicate(_) => false [owise] or predicate(#klabel(`klabel`)) => true.", r);
            }
            kseq = (KSequence) function.items().get(0);
            if (kseq.items().size() != 1 || !(kseq.items().get(0) instanceof InjectedKLabel)) {
                throw KEMException.compilerError("Unexpected form for klabel predicate rule, expected predicate(_) => false [owise] or predicate(#klabel(`klabel`)) => true.", r);
            }
            InjectedKLabel injection = (InjectedKLabel) kseq.items().get(0);
            if (injection.klabel() instanceof KVariable) {
                throw KEMException.compilerError("Unexpected form for klabel predicate rule, expected predicate(_) => false [owise] or predicate(#klabel(`klabel`)) => true.", r);
            }
            labels.add(injection.klabel());
        }
        return labels;
    }

    Table<Sort, KLabel, Boolean> sortContainsConstructorTable = HashBasedTable.create();

    // if lbl is at the top of the k cell, we know we do not have to match any rules
    // with a variable at the top of the k cell for which the variable is tagged
    // with a sort that does not contain any constructors with that label.
    // we also do not have to match any rules with a variable at the top of the k cell
    // which is governed by a klabel predicate that does not include lbl.
    private List<Rule> filterNoneRulesByVariableType(KLabel lbl, List<Rule> unfilteredRules, SetMultimap<KLabel, Rule> functionRules) {
        List<Rule> res = new ArrayList<>();
        for (Rule r : unfilteredRules) {
           Optional<KApply> kCell = hasKCellContents(RewriteToTop.toLeft(r.body()));
           if (kCell.isPresent()) {
               KSequence seq = (KSequence) kCell.get().klist().items().get(0);
               K topOfKCell = seq.items().get(0);
               if (topOfKCell instanceof KVariable) {
                       Optional<Sort> sortAtt = topOfKCell.att().getOptional(Sort.class);
                   if (sortAtt.isPresent()) {
                       Sort sort = sortAtt.get();
                       if (!sortContainsConstructorTable.contains(sort, lbl)) {
                           sortContainsConstructorTable.put(sort, lbl, sortContainsConstructor(sort, lbl, functionRules));
                       }
                       if (sortContainsConstructorTable.get(sort, lbl)) {
                           res.add(r);
                       }
                   } else {
                       res.add(r);
                   }
               } else if (topOfKCell instanceof KApply) {
                   KLabel topOfKCellLabel = ((KApply)topOfKCell).klabel();
                   if (topOfKCellLabel instanceof KVariable) {
                       KVariable var = (KVariable) topOfKCellLabel;
                       if (var.att().contains("klabelPredicate")) {
                           Set<KLabel> klabelsThatCouldMatchThisVariable = new HashSet<>(klabelsForEachPredicate.get(var.att().get("klabelPredicate")));
                           if (klabelsThatCouldMatchThisVariable.contains(lbl)) {
                               res.add(r);
                           }
                       } else {
                           res.add(r);
                       }
                   } else {
                       res.add(r);
                   }
               }
           } else {
               res.add(r);
           }
        }
        return res;
    }

    private boolean sortContainsConstructor(Sort sort, KLabel lbl, SetMultimap<KLabel, Rule> functionRules) {
        if (sort.equals(Sorts.K()) || sort.equals(Sorts.KItem())) {
            return true;
        }
        KLabel predicate = KLabel("is" + sort.toString());
        Set<Rule> rulesForSort = functionRules.get(predicate);
        for (Rule r : rulesForSort) {
            K lhs = RewriteToTop.toLeft(r.body());
            K rhs = RewriteToTop.toRight(r.body());
            if (rhs.equals(KSequence(BooleanUtils.FALSE))) {
                continue;
            }
            K body = ((KSequence)((KApply)((KSequence)lhs).items().get(0)).klist().items().get(0)).items().get(0);
            if (body instanceof KApply) {
                KLabel innerLabel = ((KApply)body).klabel();
                if (innerLabel instanceof KVariable) {
                    KVariable var = (KVariable)innerLabel;
                    if (var.att().contains("klabelPredicate")) {
                        Set<KLabel> klabelsThatCouldMatchThisVariable = new HashSet<>(klabelsForEachPredicate.get(var.att().get("klabelPredicate")));
                        if (klabelsThatCouldMatchThisVariable.contains(lbl)) {
                            return true;
                        }
                    } else {
                        // we don't know which klabel this matches, so we need to assume that this rule could match
                        return true;
                    }
                } else if (((KApply)body).klabel().equals(lbl)) {
                    return true;
                }
            } else if (body instanceof KVariable) {
                throw KEMException.internalError("not expecting a predicate rule to match a variable", body);
            }
        }
        return false;
    }

    private int writeStepFunction(StringBuilder sb, List<Rule> sortedRules, String funcName, int ruleNum) {
        Map<Boolean, List<Rule>> groupedByLookup = sortedRules.stream()
                .collect(Collectors.groupingBy(this::hasLookups));
        sb.append("and ").append(funcName).append(" (c:k) : k * step_function =\n");
        if (options.checkRaces) {
            sb.append(" let (k, (i,_ ,_), s) as kis = one_").append(funcName).append(" c (-1) in ");
            sb.append("\n    let (k,i,s) = List.hd (RACE.valid_continuations (kis :: RACE.all_steps one_").append(funcName).append(" c i)) in (k,s)\n");
            sb.append("and one_").append(funcName).append(" (c: k) (start_after: int) : k * (int * RACE.rule_type * string) * step_function =\n");
        }
        sb.append(" try let config = c in match c with \n");
        if (groupedByLookup.containsKey(false)) {
            for (Rule r : groupedByLookup.get(false)) {
                ruleNum = convert(r, sb, RuleType.REGULAR, ruleNum, funcName);
            }
        }
        sb.append("| _ -> lookups_").append(funcName).append(" c c ").append(options.checkRaces ? "start_after" : "(-1)").append('\n');
        sb.append("with Sys.Break -> raise (Stuck c)\n");
        sb.append("and lookups_").append(funcName).append(" (c: k) (config: k) (guard: int) : k ")
                .append(options.checkRaces ? "* (int * RACE.rule_type * string) " : "").append("* step_function = match c with \n");
        ruleNum = convert(groupedByLookup.getOrDefault(true, Collections.emptyList()), sb, funcName, "lookups_" + funcName, RuleType.REGULAR, ruleNum);
        sb.append("| _ -> raise (Stuck c)\n");
        return ruleNum;
    }

    private List<Rule> getRulesForStepFunction(List<Rule> rulesWithoutLookup, KLabel l) {
        List<Rule> res = new ArrayList<>();
        for (Rule r : rulesWithoutLookup) {
            Optional<KLabel> nextOp = getNextOperation(RewriteToTop.toLeft(r.body()), false);
            if (!nextOp.isPresent() || nextOp.get().equals(l)) {
                res.add(r);
            }
        }
        return res;
    }

    /**
     * Encodes the code to take all function calls to this function and memoize them
     * by looking in a private hashtable before trying to compute them again.
     * @param sb
     * @param conn
     * @param functionLabel
     * @param functionName
     * @param arity
     */
    private void encodeMemoizationOfFunction(StringBuilder sb, String conn, KLabel functionLabel, String functionName, int arity) {
        sb.append(conn.equals("let rec ") ? "and " : conn);
        sb.append("memo_table");
        encodeStringToAlphanumeric(sb, functionLabel.name());
        sb.append(" : k KMemoIdentityHashtbl.t = KMemoIdentityHashtbl.create 256\n");
        sb.append(conn.equals("let rec ") ? "and " : conn);
        encodeStringToFunction(sb, functionLabel);
        printFunctionParams(sb, arity);
        sb.append(" (config: k) (guard: int) : k = let key = ");
        sb.append("[denormalize (KApply(");
        encodeStringToIdentifier(sb, functionLabel);
        sb.append(", (denormalize").append(arity).append(" c)))]in\n ");
        sb.append("try KMemoIdentityHashtbl.find memo_table");
        encodeStringToAlphanumeric(sb, functionLabel.name());
        sb.append(" key with Not_found -> let res = ")
                .append(functionName)
                .append(" c config guard in (if KMemoIdentityHashtbl.length memo_table");
        encodeStringToAlphanumeric(sb, functionLabel.name());
        sb.append(" > (1 lsl 18) then KMemoIdentityHashtbl.clear memo_table");
        encodeStringToAlphanumeric(sb, functionLabel.name());
        sb.append(" else ()); KMemoIdentityHashtbl.add memo_table");
        encodeStringToAlphanumeric(sb, functionLabel.name());
        sb.append(" key res; res\n");
    }

    private List<List<KLabel>> sortFunctions(SetMultimap<KLabel, Rule> functionRules) {
        BiMap<KLabel, Integer> mapping = HashBiMap.create();
        int counter = 0;
        for (KLabel lbl : functions) {
            mapping.put(lbl, counter++);
        }
        for (KLabel lbl : anywhereKLabels) {
            mapping.put(lbl, counter++);
        }
        mapping.put(KLabel(""), counter++); //use blank klabel to simulate dependencies on eval
        List<Integer>[] predecessors = new List[functions.size() + anywhereKLabels.size() + 1];
        for (int i = 0; i < predecessors.length; i++) {
            predecessors[i] = new ArrayList<>();
        }

        dependencies = new DirectedSparseGraph<>();

        class GetPredecessors extends VisitK {
            private final KLabel current;

            public GetPredecessors(KLabel current) {
                this.current = current;
            }

            @Override
            public void apply(KApply k) {
                if (functions.contains(k.klabel()) || anywhereKLabels.contains(k.klabel())) {
                    predecessors[mapping.get(current)].add(mapping.get(k.klabel()));
                    dependencies.addEdge(new Object(), current, k.klabel());
                }
                if (k.klabel() instanceof KVariable) {
                    // this function requires a call to eval, so we need to add the dummy dependency
                    predecessors[mapping.get(current)].add(mapping.get(KLabel("")));
                    dependencies.addEdge(new Object(), current, KLabel(""));
                }
                super.apply(k);
            }
        }

        for (Map.Entry<KLabel, Rule> entry : functionRules.entries()) {
            GetPredecessors visitor = new GetPredecessors(entry.getKey());
            visitor.apply(entry.getValue().body());
            visitor.apply(entry.getValue().requires());
        }

        for (KLabel label : Sets.union(functions, anywhereKLabels)) {
            String hook = mainModule.attributesFor().apply(label).<String>getOptional(Attribute.HOOK_KEY).orElse(".");

            if (mainModule.attributesFor().apply(label).contains("canTakeSteps")) {
                // this function requires a call to eval, so we need to add the dummy dependency
                predecessors[mapping.get(label)].add(mapping.get(KLabel("")));
                dependencies.addEdge(new Object(), label, KLabel(""));
            }

            if (hook.equals("KREFLECTION.fresh")) {
                for (KLabel freshFunction : iterable(mainModule.freshFunctionFor().values())) {
                    predecessors[mapping.get(label)].add(mapping.get(freshFunction));
                    dependencies.addEdge(new Object(), label, freshFunction);
                }
            }
            //eval depends on everything
            predecessors[mapping.get(KLabel(""))].add(mapping.get(label));
            dependencies.addEdge(new Object(), KLabel(""), label);
        }

        List<List<Integer>> components = new SCCTarjan().scc(predecessors);

        return components.stream().map(l -> l.stream()
                .map(i -> mapping.inverse().get(i)).collect(Collectors.toList()))
                .collect(Collectors.toList());
    }

    private transient DirectedGraph<KLabel, Object> dependencies;

    private int getArity(KLabel functionLabel) {
        Set<Integer> arities = stream(mainModule.productionsFor().apply(functionLabel)).map(Production::arity).collect(Collectors.toSet());
        if (arities.size() > 1) {
            throw KEMException.compilerError("KLabel " + functionLabel + " has multiple productions with differing arities: " + mainModule.productionsFor().apply(functionLabel));
        }
        assert arities.size() == 1;
        return arities.iterator().next();
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
                ruleNum = convert(Collections.singletonList(r), sb, functionName, functionName, type, ruleNum);
            } else {
                ruleNum = convert(r, sb, type, ruleNum, functionName);
            }
        }
    }

    private int numLookups(Rule r) {
        class Holder { int i; }
        Holder h = new Holder();
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (ConvertDataStructureToLookup.isLookupKLabel(k)) {
                    h.i++;
                }
                super.apply(k);
            }
        }.apply(r.requires());
        return h.i;
    }

    private boolean hasLookups(Rule r) {
        return numLookups(r) > 0;
    }

    private int sortFunctionRules(Rule a1, Rule a2) {
        return Boolean.compare(a1.att().contains("owise"), a2.att().contains("owise"));
    }

    private static void encodeStringToIdentifier(StringBuilder sb, KLabel name) {
        sb.append("Lbl");
        encodeStringToAlphanumeric(sb, name.name());
    }

    private static void encodeStringToIdentifier(StringBuilder sb, Sort name) {
        sb.append("Sort");
        encodeStringToAlphanumeric(sb, name.toString());
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

    private static String encodeStringToMemoFunction(StringBuilder sb, KLabel lbl) {
        StringBuilder sb2 = new StringBuilder();
        sb2.append("memo");
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

    private static String[] asciiReadableEncodingOcamlCalc() {
        String[] ocamlEncoder = Arrays.copyOf(StringUtil.asciiReadableEncodingDefault, StringUtil.asciiReadableEncodingDefault.length);
        ocamlEncoder[0x3c] = "_LT_";
        ocamlEncoder[0x3e] = "_GT_";
        ocamlEncoder[0x40] = "_AT_";
        ocamlEncoder[0x5e] = "Xor_";
        ocamlEncoder[0x5f] = "_";
        return ocamlEncoder;
    }

    public static final Pattern identChar = Pattern.compile("[A-Za-z0-9_]");
    public static String[] asciiReadableEncodingOcaml = asciiReadableEncodingOcamlCalc();

    private static void encodeStringToAlphanumeric(StringBuilder sb, String name) {
        StringUtil.encodeStringToAlphanumeric(sb, name, asciiReadableEncodingOcaml, identChar, "'");
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

    private int convert(List<Rule> rules, StringBuilder sb, String functionName, String recursionName, RuleType ruleType, int ruleNum) {
        NormalizeVariables t = new NormalizeVariables();
        Map<AttCompare, List<Rule>> grouping = rules.stream().collect(
                Collectors.groupingBy(r -> new AttCompare(t.normalize(RewriteToTop.toLeft(r.body())), Sort.class.getName())));
        Map<Tuple3<AttCompare, KLabel, AttCompare>, List<Rule>> groupByFirstPrefix = new HashMap<>();
        for (Map.Entry<AttCompare, List<Rule>> entry : grouping.entrySet()) {
            AttCompare left = entry.getKey();
            groupByFirstPrefix.putAll(entry.getValue().stream()
                    .collect(Collectors.groupingBy(r -> {
                        KApply lookup = getLookup(r, 0);
                        if (lookup == null) return null;
                        //reconstruct the denormalization for this particular rule
                        K left2 = t.normalize(RewriteToTop.toLeft(r.body()));
                        K normal = t.normalize(t.applyNormalization(lookup.klist().items().get(1), left2), left2);
                        return Tuple3.apply(left, lookup.klabel(), new AttCompare(normal, Sort.class.getName()));
                    })));
        }
        List<Rule> owiseRules = new ArrayList<>();
        for (Map.Entry<Tuple3<AttCompare, KLabel, AttCompare>, List<Rule>> entry2 : groupByFirstPrefix.entrySet().stream().sorted((e1, e2) -> Integer.compare(e2.getValue().size(), e1.getValue().size())).collect(Collectors.toList())) {
            if (entry2.getValue().size() != 1 && entry2.getValue().stream().allMatch(r -> indexesPoorly(r) || r.att().contains("owise"))) {
              // no rules will actually be part of this lookup key, therefore we should elide the entire match case
              owiseRules.addAll(entry2.getValue());
              continue;
            }
            K left = entry2.getKey()._1().get();
            VarInfo globalVars = new VarInfo();
            sb.append("| ");
            convertLHS(sb, ruleType, left, globalVars);
            K lookup;
            int maxRuleNum = ruleNum + entry2.getValue().size() - 1;
            assert maxRuleNum >= ruleNum;
            sb.append(" when guard < ").append(maxRuleNum);
            if (entry2.getValue().size() == 1) {
                Rule r = entry2.getValue().get(0);
                try {
                    convertComment(r, sb);

                    //reconstruct the denormalization for this particular rule
                    left = t.normalize(RewriteToTop.toLeft(r.body()));
                    lookup = t.normalize(t.applyNormalization(getLookup(r, 0).klist().items().get(1), left), left);
                    r = t.normalize(t.applyNormalization(r, left, lookup));

                    List<Lookup> lookups = convertLookups(r.requires(), globalVars, recursionName, ruleNum, false, numLookups(r) > 1, ruleType);
                    String suffix = convertSideCondition(sb, r.requires(), globalVars, lookups, lookups.size() > 0, ruleType, ruleNum);
                    sb.append(" -> ");
                    convertRHS(sb, ruleType, r, globalVars, suffix, ruleNum, functionName, true);
                    ruleNum++;
                } catch (KEMException e) {
                    e.exception.addTraceFrame("while compiling rule at " + r.att().getOptional(Source.class).map(Object::toString).orElse("<none>") + ":" + r.att().getOptional(Location.class).map(Object::toString).orElse("<none>"));
                    throw e;
                }
            } else {
                boolean hasMultipleLookups = entry2.getValue().stream().anyMatch(r -> numLookups(r) > 1);
                Lookup head = convertLookups(KApply(entry2.getKey()._2(),
                                KToken("dummy", Sort("Dummy")), entry2.getKey()._3().get()),
                        globalVars, recursionName, maxRuleNum, true, hasMultipleLookups, ruleType).get(0);
                globalVars.termCache.remove(KToken("dummy", Sort("Dummy")));
                sb.append(head.prefix);
                for (Rule r : entry2.getValue()) {
                    if (indexesPoorly(r) || r.att().contains("owise")) {
                        owiseRules.add(r);
                    } else {
                        try {
                            convertComment(r, sb);

                            //reconstruct the denormalization for this particular rule
                            left = t.normalize(RewriteToTop.toLeft(r.body()));
                            lookup = t.normalize(t.applyNormalization(getLookup(r, 0).klist().items().get(1), left), left);
                            r = t.normalize(t.applyNormalization(r, left, lookup));

                            VarInfo vars = new VarInfo(globalVars);
                            List<Lookup> lookups = convertLookups(r.requires(), vars, recursionName, ruleNum, true, hasMultipleLookups, ruleType);
                            sb.append(lookups.get(0).pattern);
                            lookups.remove(0);
                            sb.append(" when guard < ").append(ruleNum);
                            if (options.profileRules && ruleType == RuleType.REGULAR) {
                                sb.append("&& ((print_string \"trying ").append(ruleType.name().toLowerCase()).append(" rule ").append(ruleNum).append("\\n\");true)");
                            }
                            String suffix = convertSideCondition(sb, r.requires(), vars, lookups, lookups.size() > 0, ruleType, ruleNum);
                            sb.append(" -> ");
                            convertRHS(sb, ruleType, r, vars, suffix, ruleNum, functionName, true);
                            ruleNum++;
                        } catch (KEMException e) {
                            e.exception.addTraceFrame("while compiling rule at " + r.att().getOptional(Source.class).map(Object::toString).orElse("<none>") + ":" + r.att().getOptional(Location.class).map(Object::toString).orElse("<none>"));
                            throw e;
                        }
                    }
                }
                assert ruleNum <= maxRuleNum + 1;
                ruleNum = maxRuleNum + 1;
                sb.append(head.suffix);
                sb.append("\n");
            }
        }
        for (Rule r : owiseRules) {
            try {
                VarInfo globalVars = new VarInfo();
                sb.append("| ");
                convertLHS(sb, ruleType, RewriteToTop.toLeft(r.body()), globalVars);
                sb.append(" when guard < ").append(ruleNum);
                if (options.profileRules && ruleType == RuleType.REGULAR) {
                    sb.append("&& ((print_string \"trying ").append(ruleType.name().toLowerCase()).append(" rule ").append(ruleNum).append("\\n\");true)");
                }

                convertComment(r, sb);
                List<Lookup> lookups = convertLookups(r.requires(), globalVars, recursionName, ruleNum, false, numLookups(r) > 1, ruleType);
                String suffix = convertSideCondition(sb, r.requires(), globalVars, lookups, lookups.size() > 0, ruleType, ruleNum);
                sb.append(" -> ");
                convertRHS(sb, ruleType, r, globalVars, suffix, ruleNum, functionName, true);
                ruleNum++;
            } catch (KEMException e) {
                e.exception.addTraceFrame("while compiling rule at " + r.att().getOptional(Source.class).map(Object::toString).orElse("<none>") + ":" + r.att().getOptional(Location.class).map(Object::toString).orElse("<none>"));
                throw e;
            }
        }
        return ruleNum;
    }

    private void appendStepFunction(StringBuilder sb, RuleType ruleType, Rule r, int ruleNum, String functionName) {
        if (ruleType == RuleType.REGULAR) {
            if (options.checkRaces) {
                String location = enquoteString(r.att().getOptional(Source.class).map(Object::toString).orElse("<none>") + ":" + r.att().getOptional(Location.class).map(Object::toString).orElse("<none>"));
                sb.append("), ((").append(ruleNum).append("), ").append(getRaceRuleType(r)).append(", ").append(location);
            }
            sb.append("), (StepFunc ");
            K right = RewriteToTop.toRight(r.body());
            Optional<KLabel> next = getNextOperation(right, true);
            if (next.isPresent()) {
                sb.append(realStepFunctions.get(next.get()));
            } else {
                Optional<KApply> kCell = hasKCellContents(right);
                if(kCell.isPresent()) {
                    sb.append("(get_next_op_from_exp kCell)");
                } else if (!hasKCellContents(RewriteToTop.toLeft(r.body())).isPresent()) {
                    sb.append(functionName);
                } else {
                    sb.append("step");
                }
            }
            sb.append("))");
        }
    }

    private String getRaceRuleType(Rule r) {
        Att att = r.att();
        if (att.contains("owise")) {
            return "RACE.Owise";
        }
        if (att.contains("cool")) {
            return "RACE.Cool";
        }
        if (att.contains("heat")) {
            return "RACE.Heat";
        }
        if (att.contains("nondet")) {
            return "RACE.Nondet";
        }
        return "RACE.NoType";
    }

    private Optional<KApply> hasKCellContents(K body) {
        if (!options.optimizeStep()) return Optional.empty();
        List<KApply> kCells = new ArrayList<>();
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (k.klabel().name().equals("<k>")) {
                    if (k.klist().items().size() == 1) {
                        if (k.klist().items().get(0) instanceof KSequence) {
                            KSequence seq = (KSequence) k.klist().items().get(0);
                            if (seq.items().size() >= 1) {
                                kCells.add(k);
                            }
                        }
                    }
                }
                super.apply(k);
            }
        }.apply(body);
        if (kCells.size() == 1)
            return Optional.of(kCells.get(0));
        return Optional.empty();
    }

    private boolean indexesPoorly(Rule r) {
        class Holder { boolean b; }
        Holder h = new Holder();
        VisitK visitor = new VisitK() {
            @Override
            public void apply(KApply k) {
                if (k.klabel().name().equals("<k>")) {
                    if (k.klist().items().size() == 1) {
                        if (k.klist().items().get(0) instanceof KSequence) {
                            KSequence kCell = (KSequence) k.klist().items().get(0);
                            if (kCell.items().size() == 2 && kCell.items().get(1) instanceof KVariable) {
                                K head = kCell.items().get(0);
                                while (head instanceof KAs) {
                                    head = ((KAs) head).pattern();
                                }
                                if (head instanceof KVariable) {
                                    Sort s = head.att().getOptional(Sort.class).orElse(Sort(""));
                                    if (mainModule.sortAttributesFor().contains(s)) {
                                        String hook = mainModule.sortAttributesFor().apply(s).<String>getOptional("hook").orElse("");
                                        if (!sortVarHooks.containsKey(hook)) {
                                            h.b = true;
                                        }
                                    } else {
                                        h.b = true;
                                    }
                                } else if (head instanceof KApply) {
                                    KApply kapp = (KApply) head;
                                    if (kapp.klabel() instanceof KVariable) {
                                        h.b = true;
                                    }
                                }
                            }
                        }
                    }
                }
                super.apply(k);
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
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (h.i > idx)
                    return;
                if (k.klabel().name().equals("#match")
                        || k.klabel().name().equals("#setChoice")
                        || k.klabel().name().equals("#mapChoice")
                        || k.klabel().name().equals("#filterMapChoice")) {
                    h.lookup = k;
                    h.i++;
                }
                super.apply(k);
            }
        }.apply(r.requires());
        return h.lookup;
    }

    private int convert(Rule r, StringBuilder sb, RuleType type, int ruleNum, String functionName) {
        try {
            convertComment(r, sb);
            sb.append("| ");
            K left = RewriteToTop.toLeft(r.body());
            K requires = r.requires();
            VarInfo vars = new VarInfo();
            convertLHS(sb, type, left, vars);
            String result = convert(vars);
            String suffix = "";
            boolean when = true;
            if (type == RuleType.REGULAR && options.checkRaces) {
                sb.append(" when start_after < ").append(ruleNum);
                when = false;
            }
            if (!requires.equals(KSequence(BooleanUtils.TRUE)) || !result.equals("true")) {
                suffix = convertSideCondition(sb, requires, vars, Collections.emptyList(), when, type, ruleNum);
            }
            sb.append(" -> ");
            convertRHS(sb, type, r, vars, suffix, ruleNum, functionName, true);
            return ruleNum + 1;
        } catch (NoSuchElementException e) {
            System.err.println(r);
            throw e;
        } catch (KEMException e) {
            e.exception.addTraceFrame("while compiling rule at " + r.att().getOptional(Source.class).map(Object::toString).orElse("<none>") + ":" + r.att().getOptional(Location.class).map(Object::toString).orElse("<none>"));
            throw e;
        }
    }

    private Optional<KLabel> getNextOperation(K side, boolean rhs) {
        if (!options.optimizeStep()) return Optional.empty();
        final List<KLabel> nextOps = new ArrayList<>();
        MutableBoolean hasProblem = new MutableBoolean(false);
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (k.klabel().name().equals("<k>")) {
                    if (!hasProblem.booleanValue()) {
                        hasProblem.setTrue();
                        if (k.klist().items().size() == 1) {
                            if (k.klist().items().get(0) instanceof KSequence) {
                                KSequence seq = (KSequence) k.klist().items().get(0);
                                if (seq.items().size() >= 1) {
                                    K head = seq.items().get(0);
                                    while (head instanceof KAs) {
                                        head = ((KAs) head).pattern();
                                    }
                                    if (head instanceof KApply) {
                                        KApply app = (KApply) head;
                                        if (!(app.klabel() instanceof KVariable)) {
                                            if (!rhs || (!functions.contains(app.klabel()) && !anywhereKLabels.contains(app.klabel()))) {
                                                nextOps.add(app.klabel());
                                                hasProblem.setFalse();
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                super.apply(k);
            }
        }.apply(side);
        if (nextOps.size() == 1 && !hasProblem.booleanValue())
            return Optional.of(nextOps.get(0));
        return Optional.empty();
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
        sb.append("(*{| rule ");
        sb.append(ToKast.apply(r.body()).replace("|}", "| )"));
        sb.append(" requires ");
        sb.append(ToKast.apply(r.requires()).replace("|)", "| )"));
        sb.append(" ensures ");
        sb.append(ToKast.apply(r.ensures()).replace("|)", "| )"));
        sb.append(" ");
        sb.append(r.att().toString().replace("|)", "| )"));
        sb.append("|}*)\n");
    }

    private void convertRHS(StringBuilder sb, RuleType type, Rule r, VarInfo vars, String suffix, int ruleNum, String functionName, boolean appendStepFunction) {
        K right = RewriteToTop.toRight(r.body());
        if (options.profileRules && type == RuleType.REGULAR) {
            sb.append("print_string \"succeeded ").append(type.name().toLowerCase()).append(" rule ").append(ruleNum).append("\\n\"; ");
        }
        /*if (type == RuleType.ANYWHERE) {
            sb.append("(match ");
        }*/
        Optional<KApply> kCell = Optional.empty();
        if (type == RuleType.REGULAR && appendStepFunction) {
            Optional<KLabel> next = getNextOperation(right, true);
            if (!next.isPresent()) {
                kCell = hasKCellContents(right);
            }
        }
        if (kCell.isPresent()) {
            sb.append("let kCell = ");
            convert(sb, true, vars, false, false).apply(kCell.get());
            sb.append(" in ");
            vars.termCache.put(KSequence(kCell.get()), "[kCell]");
        }
        if (type == RuleType.REGULAR && appendStepFunction) {
            sb.append("((");
        }
        if (type == RuleType.PATTERN) {
            for (KVariable var : vars.vars.keySet()) {
                sb.append("(Subst.add \"").append(getVarName(var)).append("\" ");
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
            for (KVariable ignored : vars.vars.keySet()) {
                sb.append(")");
            }
        } else {
            convert(sb, true, vars, false, false).apply(right);
            if (appendStepFunction) {
                appendStepFunction(sb, type, r, ruleNum, functionName);
            }
        }
        /*if (type == RuleType.ANYWHERE) {
            sb.append(" with [item] -> eval (normalize item) config)");
        }*/
        sb.append(suffix);
        sb.append("\n");
    }

    private String getVarName(KVariable var) {
        if (var.att().contains("denormal")) {
            return var.att().get("denormal");
        }
        return var.name();
    }

    private String convertSideCondition(StringBuilder sb, K requires, VarInfo vars, List<Lookup> lookups, boolean when, RuleType type, int ruleNum) {
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

    private List<Lookup> convertLookups(K requires, VarInfo vars, String functionName, int ruleNum, boolean hasMultipleRules, boolean hasMultipleLookups, RuleType type) {
        List<Lookup> results = new ArrayList<>();
        Holder h = new Holder();
        h.first = hasMultipleRules;
        h.reapply = "(" + functionName + " c config " + ruleNum + ")";
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (k.klabel().name().equals("#match")) {
                    if (k.klist().items().size() != 2) {
                        throw KEMException.internalError("Unexpected arity of lookup: " + k.klist().size(), k);
                    }
                    StringBuilder sb = new StringBuilder();
                    sb.append(" -> (let e = ");
                    convert(sb, true, vars, false, false).apply(k.klist().items().get(1));
                    sb.append(" in ");
                    if (h.first) {
                        if (hasMultipleLookups) {
                            sb.append("let rec ");
                        } else {
                            sb.append("let ");
                        }
                        sb.append("stepElt = fun guard -> ");
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
                        suffix += " in stepElt guard";
                        h.reapply = "(stepElt " + ruleNum + ")";
                    }
                    suffix += ")";
                    results.add(new Lookup(prefix, pattern, suffix));
                    h.first = false;
                } else if (k.klabel().name().equals("#setChoice")) {
                    if (type == RuleType.REGULAR) {
                        chooseStep(k, "| [Set (_,_,collection)] -> let " + racePair("choice", "f") + " = " +
                                "(KSet.fold (fun e " + racePair("result","f") + " -> ", "");
                    } else {
                        choose(k, "| [Set (_,_,collection)] -> let choice = (KSet.fold (fun e result -> ", "");
                    }
                } else if (k.klabel().name().equals("#mapChoice")) {
                    if (type == RuleType.REGULAR) {
                        chooseStep(k, "| [Map (_,_,collection)] -> let " + racePair("choice", "f") + " = " +
                                "(KMap.fold (fun e v " + racePair("result","f") + " -> ", "");
                    } else {
                        choose(k, "| [Map (_,_,collection)] -> let choice = (KMap.fold (fun e v result -> ", "");
                    }
                } else if (k.klabel().name().equals("#filterMapChoice")) {
                    if (type == RuleType.REGULAR) {
                        chooseStep(k, "| [Map (_,_,collection)] -> let " + racePair("choice", "f") + " = " +
                                        "(KMap.fold (fun _ pair " + racePair("result", "f")+ " -> (match pair with\n| [KApply2(_, e, v)] -> (",
                                ")\n| _ -> " + getBottom() + ")");
                    } else {
                        choose(k, "| [Map (_,_,collection)] -> let choice = (KMap.fold (fun _ pair result -> (match pair with\n| [KApply2(_, e, v)] -> (",
                                ")\n | _ -> interned_bottom)");
                    }
                }
                super.apply(k);
            }

            private String racePair(String choice, String function) {
                return "(" + choice + (options.checkRaces ? ", rule_id, " : ", ") + function + ")";
            }

            private void choose(KApply k, String choiceString, String afterElse) {
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
                    if (hasMultipleLookups) {
                        sb.append("let rec ");
                    } else {
                        sb.append("let ");
                    }
                    sb.append("stepElt = fun guard -> ");
                }
                sb.append("if result == interned_bottom then (match e with ");
                String prefix = sb.toString();
                sb = new StringBuilder();
                String suffix2 = "| _ -> interned_bottom) else result" + (h.first ? " in stepElt guard" : "") + afterElse + ") collection interned_bottom) in if choice == interned_bottom then " + h.reapply + " else choice";
                String suffix = suffix2 + "| _ -> " + h.reapply + ")";
                if (h.first) {
                    h.reapply = "(stepElt " + ruleNum + ")";
                } else {
                    h.reapply = "interned_bottom";
                }
                sb.append("| ");
                convert(sb, false, vars, false, false).apply(k.klist().items().get(0));
                sb.append(" as e").append(choiceCounter++);
                String pattern = sb.toString();
                results.add(new Lookup(prefix, pattern, suffix));
                h.first = false;
            }

            private void chooseStep(KApply k, String choiceString, String afterElse) {
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
                    if (hasMultipleLookups) {
                        sb.append("let rec ");
                    } else {
                        sb.append("let ");
                    }
                    sb.append("stepElt = fun guard -> ");
                }
                sb.append("if result == interned_bottom then (match e with ");
                String prefix = sb.toString();
                sb = new StringBuilder();
                String suffix2 = "| _ -> " + getBottom() + ") else " + racePair("result", "f")
                        + (h.first ? " in stepElt guard" : "") + afterElse + ") collection "
                        + getBottom() + ") in if choice == interned_bottom then " + h.reapply
                        + " else " + racePair("choice", "f");
                String suffix = suffix2 + "| _ -> " + h.reapply + ")";
                if (h.first) {
                    h.reapply = "(stepElt " + ruleNum + ")";
                } else {
                    h.reapply = getBottom();
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

    private String getBottom() {
        String bottom;
        if (options.checkRaces) {
            bottom = "(interned_bottom, (-1, RACE.NoType, \"\"), (StepFunc step))";
        } else {
            bottom = "(interned_bottom, (StepFunc step))";
        }
        return bottom;
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
        if (vars.vars.get(v).isEmpty() && !getVarName(v).startsWith("?")) {
            throw KEMException.internalError("Failed to compile rule due to unmatched variable on right-hand-side. This is likely due to an unsupported collection pattern: " + getVarName(v), v);
        } else if (vars.vars.get(v).isEmpty()) {
            sb.append("(raise (Stuck config))");
        } else {
            applyVarRhs(vars.vars.get(v).iterator().next(), sb, vars.listVars.get(vars.vars.get(v).iterator().next()));
        }
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

    private void applyVarLhs(KVariable k, StringBuilder sb, VarInfo vars, boolean inOr) {
        String varName;
        if (inOr && k.att().contains("anonymous")) {
            sb.append("_");
            return;
        } else if (inOr) {
            StringBuilder sb2 = new StringBuilder();
            sb2.append("var");
            encodeStringToAlphanumeric(sb2, k.name());
            varName = sb2.toString();
        } else {
            varName = encodeStringToVariable(k.name());
        }
        vars.vars.put(k, varName);
        Sort s = k.att().getOptional(Sort.class).orElse(Sort(""));
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

    private class Visitor extends VisitK {
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
        private boolean inOr = false;

        @Override
        public void apply(KApply k) {
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
                return;
            }
            if (k.klabel().equals(KLabels.ML_OR)) {
                sb.append("((");
                boolean wasInOr = inOr;
                inOr = true;
                apply(k.items().get(0));
                sb.append(")|(");
                apply(k.items().get(1));
                inOr = wasInOr;
                sb.append("))");
                return;
            }
            if (ConvertDataStructureToLookup.isLookupKLabel(k)) {
                apply(BooleanUtils.TRUE);
            } else if (k.klabel().name().equals("#KToken")) {
                //magic down-ness
                sb.append("KToken (");
                Sort sort = Outer.parseSort(((KToken) ((KSequence) k.klist().items().get(0)).items().get(0)).s());
                apply(sort);
                sb.append(", ");
                apply(((KSequence) k.klist().items().get(1)).items().get(0));
                sb.append(")");
            } else if (k.klabel().name().equals("#Bottom")) {
                sb.append("Bottom");
            } else if (k.klabel().name().equals("#ThreadLocal")) {
                sb.append("ThreadLocal");
            } else if (k.klabel().name().equals("#Thread")) {
                sb.append("Thread(");
                applyTuple(k.klist().items());
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
                    if (k.klist().size() == 0 && rhs) {
                        //intern constants for faster comparison
                        sb.append("const");
                        encodeStringToAlphanumeric(sb, k.klabel().name());
                    } else {
                        sb.append("KApply").append(k.klist().size()).append("(");
                        apply(k.klabel());
                        if (k.klist().size() > 0) {
                            sb.append(",");
                            applyTuple(k.klist().items());
                        }
                        sb.append(")");
                    }
                }
            }
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
            switch (hook) {
            case "BOOL.and":
            case "BOOL.andThen":
                assert k.klist().items().size() == 2;
                if (!stack) {
                    sb.append("[Bool (");
                }
                inBooleanExp = true;
                sb.append("((");
                apply(k.klist().items().get(0));
                sb.append(") && (");
                apply(k.klist().items().get(1));
                sb.append("))");
                if (!stack) {
                    sb.append(")]");
                }
                break;
            case "BOOL.or":
            case "BOOL.orElse":
                assert k.klist().items().size() == 2;
                if (!stack) {
                    sb.append("[Bool (");
                }
                inBooleanExp = true;
                sb.append("((");
                apply(k.klist().items().get(0));
                sb.append(") || (");
                apply(k.klist().items().get(1));
                sb.append("))");
                if (!stack) {
                    sb.append(")]");
                }
                break;
            case "BOOL.not":
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
                break;
            case "KEQUAL.ite":
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
                break;
            default:
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
                                KVariable var = (KVariable) component;
                                String varName = encodeStringToVariable(var.name());
                                vars.vars.put(var, varName);
                                vars.listVars.put(varName, collectionLabel);
                                sb.append(varName);
                                frame = true;
                            } else if (component instanceof KApply) {
                                KApply kapp = (KApply) component;
                                boolean needsWrapper = false;
                                if (kapp.klabel().equals(KLabel(attr.get("element")))
                                        || (needsWrapper = kapp.klabel().equals(KLabel(attr.get("wrapElement"))))) {
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
                if (mainModule.attributesFor().apply(k.klabel()).contains(Attribute.PREDICATE_KEY, Sort.class)) {
                    Sort s = mainModule.attributesFor().apply(k.klabel()).get(Attribute.PREDICATE_KEY, Sort.class);
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
                                    Optional<Sort> varSort = item.items().get(0).att().getOptional(Sort.class);
                                    if (varSort.isPresent() && varSort.get().equals(s)) {
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
                if (k.klist().items().size() > 0 || !constants.contains(k.klabel())) {
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
                break;
            }
            inBooleanExp = stack;
        }

        @Override
        public void apply(KAs k) {
            sb.append("(");
            apply(k.pattern());
            sb.append(" as ");
            apply(k.alias());
            sb.append(")");
        }

        @Override
        public void apply(KRewrite k) {
            throw new AssertionError("unexpected rewrite");
        }

        @Override
        public void apply(KToken k) {
            if (inBooleanExp && k.sort().equals(Sorts.Bool())) {
                sb.append(k.s());
                return;
            }
            if (mainModule.sortAttributesFor().contains(k.sort())) {
                String hook = mainModule.sortAttributesFor().apply(k.sort()).<String>getOptional("hook").orElse("");
                if (sortHooks.containsKey(hook)) {
                    sb.append(sortHooks.get(hook).apply(k.s()));
                    return;
                }
            }
            sb.append("KToken (");
            apply(k.sort());
            sb.append(", ");
            sb.append(enquoteString(k.s()));
            sb.append(")");
        }

        @Override
        public void apply(KVariable k) {
            if (inBooleanExp) {
                sb.append("(isTrue [");
            }
            if (rhs) {
                applyVarRhs(k, sb, vars);
            } else {
                applyVarLhs(k, sb, vars, inOr);
            }
            if (inBooleanExp) {
                sb.append("])");
            }
        }

        @Override
        public void apply(KSequence k) {
            if (k.items().size() == 1 && inBooleanExp) {
                apply(k.items().get(0));
                return;
            }
            if (vars.termCache.containsKey(k) && rhs) {
                sb.append(vars.termCache.get(k));
                return;
            }
            sb.append("(");
            if (!rhs) {
                for (int i = 0; i < k.items().size() - 1; i++) {
                    if (isList(k.items().get(i), false, false, vars, topAnywherePost)) {
                        throw KEMException.criticalError("Cannot compile KSequence with K variable not at tail.", k.items().get(i));
                    }
                }
            }
            apply(k.items(), false);
            sb.append(")");
        }

        @Override
        public void apply(InjectedKLabel k) {
            sb.append("InjectedKLabel (");
            apply(k.klabel());
            sb.append(")");
        }

        private void apply(List<K> items, boolean klist) {
            for (int i = 0; i < items.size(); i++) {
                K item = items.get(i);
                boolean stack = topAnywherePre;
                if (isUnit(item, klist, rhs, vars, stack)) {
                    sb.append("let _ = ");
                }
                apply(item);
                if (i != items.size() - 1) {
                    if (isUnit(item, klist, rhs, vars, stack)) {
                        sb.append(" in ");
                    } else if (isList(item, klist, rhs, vars, stack)) {
                        sb.append(" @ ");
                    } else {
                        sb.append(" :: ");
                    }
                } else {
                    if (isUnit(item, klist, rhs, vars, stack)) {
                        sb.append(" in []");
                    } else if (!isList(item, klist, rhs, vars, stack)) {
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
                Att att = ((KVariable)klabel).att();
                if (att.contains("klabelPredicate") && !rhs) {
                    List<KLabel> klabelsForPredicate = klabelsForEachPredicate.get(att.get("klabelPredicate"));
                    sb.append("(");
                    Joiner.on("|").appendTo(sb, klabelsForPredicate.stream().map(kl -> (Object)encodeStringToIdentifier(kl))::iterator);
                    sb.append(") as ");
                }
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
        if (k.att().contains("cellSort")) {
            return Sorts.K().toString();
        }
        return k.att().getOptional(Sort.class).orElse(Sorts.K()).toString();
    }

    private boolean isUnit(K item, boolean klist, boolean rhs, VarInfo vars, boolean anywhereRule) {
        return isList(item, klist, rhs, vars, anywhereRule) && item instanceof KApply && !(((KApply)item).klabel() instanceof KVariable) && mainModule.attributesFor().apply(((KApply)item).klabel()).contains("returnsUnit");
    }

    private boolean isList(K item, boolean klist, boolean rhs, VarInfo vars, boolean anywhereRule) {
        return !klist && ((item instanceof KVariable && getSortOfVar((KVariable)item, vars).equals("K")) || item instanceof KSequence
                || (item instanceof KAs && isList(((KAs) item).alias(), klist, rhs, vars, anywhereRule))
                || (item instanceof KApply && (functions.contains(((KApply) item).klabel()) || (((anywhereKLabels.contains(((KApply) item).klabel()) && !anywhereRule) || ((KApply) item).klabel() instanceof KVariable) && rhs))))
                && !(!rhs && item instanceof KApply && collectionFor.containsKey(((KApply) item).klabel()));
    }

}
