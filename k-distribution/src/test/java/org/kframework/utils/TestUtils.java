package org.kframework.utils;

import com.google.inject.AbstractModule;
import com.google.inject.Guice;
import com.google.inject.Injector;
import org.kframework.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.backend.java.symbolic.InitializeRewriter;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.convertors.TstTinyOnKORE_IT;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.function.BiFunction;



/**
 * Created by Manasvi on 6/19/15.
 *
 * Create this object to use for Tests.
 *
 * Contains utilities used across Tests.
 */
public class TestUtils {

    private CompiledDefinition compiledDef;
    private AbstractModule guiceModule;



    public TestUtils(CompiledDefinition compiledDef, AbstractModule guiceModule) {
        this.compiledDef = compiledDef;
        this.guiceModule = guiceModule;
    }

    protected File testResource(String baseName) throws URISyntaxException {
        return new File(TstTinyOnKORE_IT.class.getResource(baseName).toURI());
    }


    public K getProgram(String fileName, String program, Source source) throws IOException, URISyntaxException{
        File definitionFile = testResource(fileName);
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());

        try {
            compiledDef = new Kompile(new KompileOptions(), FileUtil.testFileUtil(), kem, false).run(definitionFile, "IMP", "IMP-SYNTAX", Sorts.K());
            BiFunction<String, Source, K> programParser = compiledDef.getProgramParser(kem);
            K parsedProgram = programParser.apply(program, source);
            return parsedProgram;
        }
        finally {
            kem.print();
        }
    }

    public Rewriter getRewriter() {
        Injector injector = Guice.createInjector(guiceModule);
        InitializeRewriter init = injector.getInstance(InitializeRewriter.class);
        return init.apply(compiledDef.executionModule());
    }

    public Module getUnparsingModule() {
        return compiledDef.getExtensionModule(Module("UNPARSING", Set(compiledDef.executionModule(), compiledDef.syntaxModule(), compiledDef.getParsedDefinition().getModule("K-SORT-LATTICE").get(), compiledDef.getParsedDefinition().getModule("KSEQ-SYMBOLIC").get()), Set(), Att()));

    }

}
