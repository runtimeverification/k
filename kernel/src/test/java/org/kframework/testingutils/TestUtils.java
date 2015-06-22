package org.kframework.testingutils;

import com.google.inject.Injector;
import org.kframework.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.backend.java.symbolic.InitializeRewriter;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.IOException;
import java.net.URISyntaxException;
import java.util.function.BiFunction;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

/**
 * Created by Manasvi on 6/19/15.
 *
 * Create this object to use for Tests.
 *
 * Contains utilities used across Tests.
 */

public class TestUtils {

    private CompiledDefinition compiledDef;
    private Injector injector;
    private KExceptionManager kem;

    public TestUtils(CompiledDefinition compiledDef, Injector injector, KExceptionManager kem) {
        this.compiledDef = compiledDef;
        this.injector = injector;
        this.kem = kem;
    }

    public K getParsed(String program, Source source) throws IOException, URISyntaxException{
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        try {
            BiFunction<String, Source, K> programParser = compiledDef.getProgramParser(kem);
            K parsedProgram = programParser.apply(program, source);
            return parsedProgram;
        }
        finally {
            kem.print();
        }
    }

    public Rewriter getRewriter() {
        InitializeRewriter init = injector.getInstance(InitializeRewriter.class);
        return init.apply(compiledDef.executionModule());
    }

    public Module getUnparsingModule() {
        return compiledDef.getExtensionModule(Module("UNPARSING", Set(compiledDef.executionModule(), compiledDef.syntaxModule(), compiledDef.getParsedDefinition().getModule("K-SORT-LATTICE").get(), compiledDef.getParsedDefinition().getModule("KSEQ-SYMBOLIC").get()), Set(), Att()));

    }

}
