// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser;
import com.davekoelle.AlphanumComparator;
import com.google.inject.Inject;
import com.google.inject.Provider;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Main;
import org.kframework.parser.InputModes;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.kore.KoreParser;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TTYInfo;
import org.kframework.utils.StringUtil;
import scala.Tuple2;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.Set;
import java.util.stream.Collectors;

import scala.Option;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;
import org.kframework.krun.*;

public class KRead {

    private final KExceptionManager kem;
    private final FileUtil files;

    @Inject
    public KRead(KExceptionManager kem, FileUtil files) {
        this.kem            = kem;
        this.files          = files;
    }

    public K prettyRead(Module mod, Sort sort, CompiledDefinition def, Source source, String stringToParse, InputModes inputMode) {
        switch (inputMode) {
            case KAST:
            case JSON:
                return deserialize(stringToParse, inputMode);
            case PROGRAM:
                return def.getParser(mod, sort, kem).apply(stringToParse, source);
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
        }
    }

    public static K deserialize(String stringToParse, InputModes inputMode) {
        K parsed;
        switch (inputMode) {
            case JSON:
                return JsonParser.parse(stringToParse);
            case KAST:
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
        }
    }

    /* Parsing code from KRun: */

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

    private K parseConfigVars(KRunOptions options, CompiledDefinition compiledDef, TTYInfo tty) {
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
        if (compiledDef.kompiledDefinition.mainModule().definedSorts().contains(Sorts.String())) {
            if (options.io()) {
                output.put(KToken("$STDIN", Sorts.KConfigVar()), KToken("\"\"", Sorts.String()));
                output.put(KToken("$IO", Sorts.KConfigVar()), KToken("\"on\"", Sorts.String()));
            } else {
                String stdin = getStdinBuffer(tty.stdin);
                output.put(KToken("$STDIN", Sorts.KConfigVar()), KToken(StringUtil.enquoteKString(stdin), Sorts.String()));
                output.put(KToken("$IO", Sorts.KConfigVar()), KToken("\"off\"", Sorts.String()));
            }
        }
        if (options.global.debug()) {
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

    public KApply plugConfigVars(CompiledDefinition compiledDef, Map<KToken, K> output) {
        return KApply(compiledDef.topCellInitializer, output.entrySet().stream().map(e -> KApply(KLabel("_|->_"), e.getKey(), e.getValue())).reduce(KApply(KLabel(".Map")), (a, b) -> KApply(KLabel("_Map_"), a, b)));
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
            buffer = "";
        }
        return buffer + "\n";
    }
}
