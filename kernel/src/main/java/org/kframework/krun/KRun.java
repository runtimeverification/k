// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.krun;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.attributes.Source;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.Main;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.kore.KoreParser;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TTYInfo;
import scala.Tuple2;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * The KORE-based KRun
 */
public class KRun {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final TTYInfo tty;
    private final KPrint kprint;

    public KRun(KExceptionManager kem, FileUtil files, TTYInfo tty, KPrint kprint) {
        this.kem    = kem;
        this.files  = files;
        this.tty    = tty;
        this.kprint = kprint;
    }

    public static class InitialConfiguration {
        public K theConfig;

        public InitialConfiguration(K theConfig) {
            this.theConfig = theConfig;
        }
    }

    public int run(CompiledDefinition compiledDef, KRunOptions options, Function<Module, Rewriter> rewriterGenerator, ExecutionMode executionMode) {
        String pgmFileName = options.configurationCreation.pgm();
        K program;
        if (options.configurationCreation.term()) {
            program = externalParse(options.configurationCreation.parser(compiledDef.executionModule().name(), files),
                    pgmFileName, compiledDef.programStartSymbol, Source.apply("<parameters>"), compiledDef);
        } else {
            program = parseConfigVars(options, compiledDef);
        }

        // store initial configuration in single mutable reference so that we can make sure it can be garbage collected
        // down the stack.
        InitialConfiguration config = new InitialConfiguration(program);
        program = null;

        Tuple2<K, Integer> result = executionMode.execute(config, rewriterGenerator, compiledDef);


        if (result != null) {
            kprint.prettyPrint(compiledDef.getParsedDefinition(), compiledDef.languageParsingModule(), compiledDef.kompileOptions, s -> kprint.outputFile(s), result._1());
            return result._2();
        }
        return 0;
    }

    /**
     * Function to return the exit code specified by the user given a substitution
     *
     * @param kem ExcpetionManager object
     * @param res The substitution from the match of the user specified pattern on the Final Configuration.
     * @return An int representing the error code.
     */
    public static int getExitCode(KExceptionManager kem, K res) {
        KApply app = (KApply) res;
        List<K> solution = Assoc.flatten(KLabels.ML_AND, app.klist().items(), KLabels.ML_TRUE);
        Set<Integer> vars = new HashSet<>();
        for (K conjunct : solution) {
            if (conjunct instanceof KApply) {
                KApply kapp = (KApply)conjunct;
                if (kapp.klabel().equals(KLabel("_==K_"))) {
                    if (kapp.items().get(0) instanceof KVariable && kapp.items().get(1) instanceof KToken) {
                        KToken rhs = (KToken) kapp.items().get(1);
                        if (Sorts.Int().equals(rhs.sort())) {
                            vars.add(Integer.valueOf(rhs.s()));
                        }
                    }
                }
            }
        }

        if (vars.size() != 1) {
            kem.registerCriticalWarning("Found " + vars.size() + " integer variables in exit code pattern. Returning 111.");
            return 111;
        }
        return vars.iterator().next();
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
    public static Rule compilePattern(FileUtil files, KExceptionManager kem, String pattern, CompiledDefinition compiledDef, Source source) {
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

    private K parseConfigVars(KRunOptions options, CompiledDefinition compiledDef) {
        HashMap<KToken, K> output = new HashMap<>();
        for (Map.Entry<String, Pair<String, String>> entry
                : options.configurationCreation.configVars(compiledDef.getParsedDefinition().mainModule().name(), files).entrySet()) {
            String name = entry.getKey();
            String value = entry.getValue().getLeft();
            String parser = entry.getValue().getRight();
            String configVarName = "$" + name;
            Sort sort = compiledDef.configurationVariableDefaultSorts.getOrDefault(configVarName, compiledDef.programStartSymbol);
            K configVar = externalParse(parser, value, sort, Source.apply("<command line: -c" + name + ">"), compiledDef);
            output.put(KToken(configVarName, Sorts.KConfigVar()), configVar);
        }
        if (options.io()) {
            output.put(KToken("$STDIN", Sorts.KConfigVar()), KToken("\"\"", Sorts.String()));
            output.put(KToken("$IO", Sorts.KConfigVar()), KToken("\"on\"", Sorts.String()));
        } else {
            String stdin = getStdinBuffer(tty.stdin);
            output.put(KToken("$STDIN", Sorts.KConfigVar()), KToken("\"" + stdin + "\"", Sorts.String()));
            output.put(KToken("$IO", Sorts.KConfigVar()), KToken("\"off\"", Sorts.String()));
        }
        if (options.global.debug) {
            // on the critical path, so don't perform this check because it's slow unless we're debugging.
            checkConfigVars(output.keySet(), compiledDef);
        }
        return plugConfigVars(compiledDef, output);
    }

    private void checkConfigVars(Set<KToken> inputConfigVars, CompiledDefinition compiledDef) {
        Set<KToken> defConfigVars = mutable(new ConfigurationInfoFromModule(compiledDef.kompiledDefinition.mainModule()).configVars());

        for (KToken defConfigVar : defConfigVars) {
            if (!inputConfigVars.contains(defConfigVar)) {
                throw KEMException.compilerError("Configuration variable missing: " + defConfigVar.s());
            }
        }

        for (KToken inputConfigVar : inputConfigVars) {
            if (!defConfigVars.contains(inputConfigVar)) {
                if (!inputConfigVar.s().equals("$STDIN") && !inputConfigVar.s().equals("$IO")) {
                    kem.registerCompilerWarning("User specified configuration variable " + inputConfigVar.s() + " which does not exist.");
                }
            }
        }
    }

    public static String getStdinBuffer(boolean ttyStdin) {
        String buffer = "";

        try {
            BufferedReader br = new BufferedReader(
                    new InputStreamReader(System.in));
            // detect if the input comes from console or redirected
            // from a pipeline

            if ((Main.isNailgun() && !ttyStdin)
                    || (!Main.isNailgun() && br.ready())) {
                buffer = br.readLine();
            }
        } catch (IOException e) {
            throw KEMException.internalError("IO error detected reading from stdin", e);
        }
        if (buffer == null) {
            return "";
        }
        return buffer + "\n";
    }

    public KApply plugConfigVars(CompiledDefinition compiledDef, Map<KToken, K> output) {
        return KApply(compiledDef.topCellInitializer, output.entrySet().stream().map(e -> KApply(KLabel("_|->_"), e.getKey(), e.getValue())).reduce(KApply(KLabel(".Map")), (a, b) -> KApply(KLabel("_Map_"), a, b)));
    }

    public K externalParse(String parser, String value, Sort startSymbol, Source source, CompiledDefinition compiledDef) {
        List<String> tokens = new ArrayList<>(Arrays.asList(parser.split(" ")));
        tokens.add(value);
        Map<String, String> environment = new HashMap<>();
        environment.put("KRUN_SORT", startSymbol.toString());
        environment.put("KRUN_COMPILED_DEF", files.resolveDefinitionDirectory(".").getAbsolutePath());
        RunProcess.ProcessOutput output = RunProcess.execute(environment, files.getProcessBuilder(), tokens.toArray(new String[tokens.size()]));

        if (output.exitCode != 0) {
            throw new ParseFailedException(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, "Parser returned a non-zero exit code: "
                    + output.exitCode + "\nStdout:\n" + new String(output.stdout) + "\nStderr:\n" + new String(output.stderr)));
        }

        byte[] kast = output.stdout != null ? output.stdout : new byte[0];
        if (BinaryParser.isBinaryKast(kast)) {
            return BinaryParser.parse(kast);
        } else {
            return KoreParser.parse(new String(kast), source);
        }
    }
}
