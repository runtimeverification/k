// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.kil.Attributes;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KToken;
import org.kframework.kore.Sort;
import org.kframework.parser.ProductionReference;
import org.kframework.transformation.Transformation;
import org.kframework.unparser.AddBrackets;
import org.kframework.unparser.KOREToTreeNodes;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;
import static org.kframework.definition.Constructors.*;

/**
 * The KORE-based KRun
 */
public class KRun implements Transformation<Void, Void> {

    private final KExceptionManager kem;
    private final FileUtil files;

    public KRun(KExceptionManager kem, FileUtil files) {
        this.kem = kem;
        this.files = files;
    }

    public int run(CompiledDefinition compiledDef, KRunOptions options, Function<Module, Rewriter> rewriterGenerator) {
        String pgmFileName = options.configurationCreation.pgm();
        K program;
        if (options.configurationCreation.term()) {
            program = externalParse(options.configurationCreation.parser(compiledDef.executionModule().name()),
                    pgmFileName, compiledDef.programStartSymbol, Source.apply("<parameters>"), compiledDef);
        } else {
            program = parseConfigVars(options, compiledDef);
        }

        Rewriter rewriter = rewriterGenerator.apply(compiledDef.executionModule());

        K result = rewriter.execute(program);

        Module mod = Module("UNPARSING", Set(compiledDef.executionModule(), compiledDef.syntaxModule(), compiledDef.getParsedDefinition().getModule("K-SORT-LATTICE").get()), Set(), Att());
        Module unparsingModule = compiledDef.getParserModule(mod).seedModule();

        System.out.println(unparseTerm(result, unparsingModule));
        return 0;
    }

    private K parseConfigVars(KRunOptions options, CompiledDefinition compiledDef) {
        HashMap<KToken, K> output = new HashMap<>();
        for (Map.Entry<String, Pair<String, String>> entry
                : options.configurationCreation.configVars(compiledDef.executionModule().name()).entrySet()) {
            String name = entry.getKey();
            String value = entry.getValue().getLeft();
            String parser = entry.getValue().getRight();
            // TODO(dwightguth): start symbols
            Sort sort = Sorts.K();
            K configVar = externalParse(parser, value, sort, Source.apply("<command line: -c" + name + ">"), compiledDef);
            output.put(KToken("$" + name, Sorts.KConfigVar()), configVar);
        }
        return plugConfigVars(compiledDef, output);
    }

    public KApply plugConfigVars(CompiledDefinition compiledDef, Map<KToken, K> output) {
        return KApply(compiledDef.topCellInitializer, output.entrySet().stream().map(e -> KApply(KLabel("_|->_"), e.getKey(), e.getValue())).reduce(KApply(KLabel(".Map")), (a, b) -> KApply(KLabel("_Map_"), a, b)));
    }

    private String unparseTerm(K input, Module test) {
        return KOREToTreeNodes.toString(
                new AddBrackets(test).addBrackets((ProductionReference)
                        KOREToTreeNodes.apply(KOREToTreeNodes.up(input), test)));
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
        return compiledDef.getParser(compiledDef.getParserModule(compiledDef.getParsedDefinition().getModule("KSEQ-SYMBOLIC").get()), Sorts.K(), kem).apply(kast, source);
    }

    @Override
    public String getName() {
        return null;
    }
}
