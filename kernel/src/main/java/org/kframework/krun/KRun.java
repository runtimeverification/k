// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.rewriter.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.backend.unparser.OutputModes;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kil.Attributes;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.ToKast;
import org.kframework.kore.compile.VisitKORE;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.parser.ProductionReference;
import org.kframework.transformation.Transformation;
import org.kframework.unparser.AddBrackets;
import org.kframework.unparser.KOREToTreeNodes;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.koreparser.KoreParser;
import scala.Tuple2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;

import static org.kframework.kore.KORE.*;

/**
 * The KORE-based KRun
 */
public class KRun implements Transformation<Void, Void> {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final boolean ttyStdin;

    public KRun(KExceptionManager kem, FileUtil files, boolean ttyStdin) {
        this.kem = kem;
        this.files = files;
        this.ttyStdin = ttyStdin;
    }

    public int run(CompiledDefinition compiledDef, KRunOptions options, Function<Module, Rewriter> rewriterGenerator, ExecutionMode executionMode) {
        String pgmFileName = options.configurationCreation.pgm();
        K program;
        if (options.configurationCreation.term()) {
            program = externalParse(options.configurationCreation.parser(compiledDef.executionModule().name()),
                    pgmFileName, compiledDef.programStartSymbol, Source.apply("<parameters>"), compiledDef);
        } else {
            program = parseConfigVars(options, compiledDef);
        }


        Rewriter rewriter = rewriterGenerator.apply(compiledDef.executionModule());

        Object result = executionMode.execute(program, rewriter, compiledDef);

        if (result instanceof K) {
            prettyPrint(compiledDef, options.output, s -> outputFile(s, options), (K) result);
            if (options.exitCodePattern != null) {
                Rule exitCodePattern = compilePattern(files, kem, options.exitCodePattern, options, compiledDef, Source.apply("<command line: --exit-code>"));
                List<? extends Map<? extends KVariable, ? extends K>> res = rewriter.match((K) result, exitCodePattern);
                return getExitCode(kem, res);
            }
        } else if (result instanceof Tuple2) {
            Tuple2<?, ?> tuple = (Tuple2<?, ?>) result;
            if (tuple._1() instanceof K && tuple._2() instanceof Integer) {
                prettyPrint(compiledDef, options.output, s -> outputFile(s, options), (K) tuple._1());
                return (Integer) tuple._2();
            }
            if (tuple._1() instanceof SearchResult && tuple._2() instanceof Integer) {
                printSearchResult((SearchResult) tuple._1(), options, compiledDef);
                return (Integer) tuple._2();
            }
        } else if (result instanceof SearchResult) {
            printSearchResult((SearchResult) result, options, compiledDef);
            return 0;
        } else if (options.experimental.prove != null) {
            if (((List) result).isEmpty()) {
                System.out.println("true");
            }
        }
        return 0;
    }

    private void printSearchResult(SearchResult result, KRunOptions options, CompiledDefinition compiledDef) {
        List<? extends Map<? extends KVariable, ? extends K>> searchResult = ((SearchResult) result).getSearchList();
        if (searchResult == null || searchResult.isEmpty()) {
            outputFile("No Search Results \n", options);
        }
        int i = 0;
        for (Map<? extends KVariable, ? extends K> substitution : searchResult) {
            outputFile("Solution: " + (i++) + "\n", options);
            prettyPrintSubstitution(substitution, result.getParsedRule(), compiledDef, options.output, s -> outputFile(s, options));
        }
    }

    /**
     * Function to return the exit code specified by the user given a substitution
     *
     * @param kem ExcpetionManager object
     * @param res The substitution from the match of the user specified pattern on the Final Configuration.
     * @return An int representing the error code.
     */
    public static int getExitCode(KExceptionManager kem, List<? extends Map<? extends KVariable, ? extends K>> res) {
        if (res.size() != 1) {
            kem.registerCriticalWarning("Found " + res.size() + " solutions to exit code pattern. Returning 112.");
            return 112;
        }
        Map<? extends KVariable, ? extends K> solution = res.get(0);
        Set<Integer> vars = new HashSet<>();
        for (K t : solution.values()) {
            // TODO(andreistefanescu): fix Token.sort() to return a kore.Sort that obeys kore.Sort's equality contract.
            if (t instanceof KToken && Sorts.Int().equals(((KToken) t).sort())) {
                try {
                    vars.add(Integer.valueOf(((KToken) t).s()));
                } catch (NumberFormatException e) {
                    throw KEMException.criticalError("Exit code found was not in the range of an integer. Found: " + ((KToken) t).s(), e);
                }
            }
        }
        if (vars.size() != 1) {
            kem.registerCriticalWarning("Found " + vars.size() + " integer variables in exit code pattern. Returning 111.");
            return 111;
        }
        return vars.iterator().next();
    }

    //TODO(dwightguth): use Writer
    public void outputFile(String output, KRunOptions options) {
        if (options.outputFile == null) {
            System.out.print(output);
        } else {
            files.saveToWorkingDirectory(options.outputFile, output);
        }
    }

    /**
     * Function to compile the String Pattern, if the pattern is not present in the cache. Note the difference between
     * compilation and parsing. Compilation is the result of resolving anonymous variables, semantic casts, and concretizing
     * sentences after parsing the pattern string.
     *
     * @param pattern The String specifying the pattern to be compiled
     * @param source  Source of the pattern, usually either command line or file path.
     * @return The pattern (represented by a Rule object) obtained from the compilation process.
     */
    public static Rule compilePattern(FileUtil files, KExceptionManager kem, String pattern, KRunOptions options, CompiledDefinition compiledDef, Source source) {
        if (pattern != null && (options.experimental.prove != null || options.experimental.ltlmc())) {
            throw KEMException.criticalError("Pattern matching is not supported by model checking or proving");
        }
        return compiledDef.compilePatternIfAbsent(files, kem, pattern, source);
    }

    /**
     * Function to parse the String Pattern. It's the step in the compilation process that occurs before resoving anonymous variables,
     * semantic casts, and sentence concretizaiton
     *
     * @param pattern The String representing the pattern to be parsed.
     * @param source  The Source of the pattern, usually either the command line or the file path.
     * @return The pattern (represented by a Rule object) obtained from the parsing process.
     */
    public static Rule parsePattern(FileUtil files, KExceptionManager kem, String pattern, CompiledDefinition compiledDef, Source source) {
        return compiledDef.parsePatternIfAbsent(files, kem, pattern, source);
    }

    public static void prettyPrint(CompiledDefinition compiledDef, OutputModes output, Consumer<String> print, K result) {
        switch (output) {
        case KAST:
            print.accept(ToKast.apply(result) + "\n");
            break;
        case NONE:
            print.accept("");
            break;
        case PRETTY:
            Module unparsingModule = compiledDef.getExtensionModule(compiledDef.languageParsingModule());
            print.accept(unparseTerm(result, unparsingModule) + "\n");
            break;
        default:
            throw KEMException.criticalError("Unsupported output mode: " + output);
        }
    }

    /**
     * Given a substitution, represented by a map of KVariables to K, print the substitution. The printing follows the following format:
     * If Pattern is represented by a single variable, then entire substitution is printed without the pattern, else
     * variable is printed, followed by --->, and then the substitution corresponding K.
     *
     * @param subst         A Map from KVariables to K representing the result of a match of a pattern on a configuration.
     * @param parsedPattern The parsed (not compiled) pattern object. The parsed pattern is used to
     *                      weed out variables not defined in the original string pattern by the user.
     * @param outputModes   The output mode represented by the user.
     * @param print         A consumer function that is called with the result of the unparsing process. The consumer must accept a String.
     */
    public static void prettyPrintSubstitution(Map<? extends KVariable, ? extends K> subst,
                                               Rule parsedPattern, CompiledDefinition compiledDefinition,
                                               OutputModes outputModes,
                                               Consumer<String> print) {
        if (subst.isEmpty()) {
            return;
        }
        List<String> varList = new ArrayList<>();
        new VisitKORE() {
            @Override
            public Void apply(KVariable k) {
                    /* Not Observing reflexivity Rule requires comparison by name */
                varList.add(k.name());
                return super.apply(k);
            }
        }.apply(parsedPattern.body());
        for (KVariable variable : subst.keySet()) {
            if (varList.contains(variable.name())) {
                K value = subst.get(variable);
                if (parsedPattern.body() instanceof KVariable) {
                    prettyPrint(compiledDefinition, outputModes, print, value);
                    return;
                }
                prettyPrint(compiledDefinition, outputModes, print, variable);
                print.accept("---> \n");
                prettyPrint(compiledDefinition, outputModes, print, value);
            }
        }
    }

    private K parseConfigVars(KRunOptions options, CompiledDefinition compiledDef) {
        HashMap<KToken, K> output = new HashMap<>();
        for (Map.Entry<String, Pair<String, String>> entry
                : options.configurationCreation.configVars(compiledDef.languageParsingModule().name()).entrySet()) {
            String name = entry.getKey();
            String value = entry.getValue().getLeft();
            String parser = entry.getValue().getRight();
            // TODO(dwightguth): start symbols
            Sort sort = Sorts.K();
            K configVar = externalParse(parser, value, sort, Source.apply("<command line: -c" + name + ">"), compiledDef);
            output.put(KToken("$" + name, Sorts.KConfigVar()), configVar);
        }
        if (options.io()) {
            output.put(KToken("$STDIN", Sorts.KConfigVar()), KToken("\"\"", Sorts.String()));
            output.put(KToken("$IO", Sorts.KConfigVar()), KToken("\"on\"", Sorts.String()));
        } else {
            String stdin = InitialConfigurationProvider.getStdinBuffer(ttyStdin);
            output.put(KToken("$STDIN", Sorts.KConfigVar()), KToken("\"" + stdin + "\"", Sorts.String()));
            output.put(KToken("$IO", Sorts.KConfigVar()), KToken("\"off\"", Sorts.String()));
        }
        return plugConfigVars(compiledDef, output);
    }

    public KApply plugConfigVars(CompiledDefinition compiledDef, Map<KToken, K> output) {
        return KApply(compiledDef.topCellInitializer, output.entrySet().stream().map(e -> KApply(KLabel("_|->_"), e.getKey(), e.getValue())).reduce(KApply(KLabel(".Map")), (a, b) -> KApply(KLabel("_Map_"), a, b)));
    }

    private static String unparseTerm(K input, Module test) {
        return KOREToTreeNodes.toString(
                new AddBrackets(test).addBrackets((ProductionReference)
                        KOREToTreeNodes.apply(KOREToTreeNodes.up(test, input), test)));
    }

    @Override
    public Void run(Void aVoid, Attributes attrs) {
        return null;
    }

    public K externalParse(String parser, String value, Sort startSymbol, Source source, CompiledDefinition compiledDef) {
        List<String> tokens = new ArrayList<>(Arrays.asList(parser.split(" ")));
        tokens.add(value);
        Map<String, String> environment = new HashMap<>();
        environment.put("KRUN_SORT", startSymbol.name());
        environment.put("KRUN_COMPILED_DEF", files.resolveDefinitionDirectory(".").getAbsolutePath());
        RunProcess.ProcessOutput output = RunProcess.execute(environment, files.getProcessBuilder(), tokens.toArray(new String[tokens.size()]));

        if (output.exitCode != 0) {
            throw new ParseFailedException(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, "Parser returned a non-zero exit code: "
                    + output.exitCode + "\nStdout:\n" + output.stdout + "\nStderr:\n" + output.stderr));
        }

        String kast = output.stdout != null ? output.stdout : "";
        return KoreParser.parse(kast, source);
    }

    @Override
    public String getName() {
        return null;
    }
}
