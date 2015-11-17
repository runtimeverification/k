// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.utils;

import com.google.inject.Guice;
import com.google.inject.Injector;
import org.kframework.backend.java.symbolic.JavaBackend;
import org.kframework.rewriter.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.backend.java.symbolic.InitializeRewriter;
import org.kframework.backend.java.symbolic.JavaSymbolicCommonModule;
import org.kframework.backend.java.symbolic.Stage;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.krun.KRun;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.DefinitionScoped;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.inject.SimpleScope;
import org.kframework.utils.options.SMTOptions;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Collections;
import java.util.Optional;
import java.util.function.BiFunction;

import static org.kframework.kore.KORE.KToken;

/**
 * Created by Manasvi on 6/19/15.
 * <p>
 * Create this object to use for Tests.
 * <p>
 * Contains utilities used across Tests.
 */

public class KoreUtils {

    public final CompiledDefinition compiledDef;
    public final Injector injector;
    public final KExceptionManager kem;
    public final SimpleScope requestScope;
    public final BiFunction<String, Source, K> programParser;
    public Rewriter rewriter;

    protected File testResource(String baseName) throws URISyntaxException {
        return new File(KoreUtils.class.getResource(baseName).toURI());
    }

    public KoreUtils(String fileName, String mainModuleName, String mainProgramsModuleName) throws URISyntaxException {
        kem = new KExceptionManager(new GlobalOptions());
        File definitionFile = testResource(fileName);
        KompileOptions kompileOptions = new KompileOptions();
        GlobalOptions globalOptions = new GlobalOptions();

        Kompile kompile = new Kompile(kompileOptions, FileUtil.testFileUtil(), kem, false);
        compiledDef = kompile.run(definitionFile, mainModuleName, mainProgramsModuleName, Sorts.K(),
                new JavaBackend(kem, FileUtil.testFileUtil(), globalOptions, kompileOptions).steps(kompile));
        requestScope = new SimpleScope();
        injector = Guice.createInjector(new JavaSymbolicCommonModule() {
            @Override
            protected void configure() {
                super.configure();
                bind(GlobalOptions.class).toInstance(globalOptions);
                bind(SMTOptions.class).toInstance(new SMTOptions());
                bind(Stage.class).toInstance(Stage.REWRITING);
                bind(FileSystem.class).to(PortableFileSystem.class);
                bind(FileUtil.class).toInstance(FileUtil.testFileUtil());
                bind(KompileOptions.class).toInstance(kompileOptions);

                bindScope(RequestScoped.class, requestScope);
                bindScope(DefinitionScoped.class, requestScope);
            }
        });
        programParser = compiledDef.getProgramParser(kem);
    }

    public K getParsed(String program, Source source) throws IOException, URISyntaxException {
        K parsed = programParser.apply(program, source);
        KRun krun = new KRun(kem, FileUtil.testFileUtil(), true);
        return krun.plugConfigVars(compiledDef, Collections.singletonMap(KToken("$PGM", Sorts.KConfigVar()), parsed));

    }

    public K stepRewrite(K parsedPgm, Optional<Integer> depth) {
        requestScope.enter();
        InitializeRewriter init = injector.getInstance(InitializeRewriter.class);
        try {
            InitializeRewriter initRewriter = injector.getInstance(InitializeRewriter.class);
            K kResult = init.apply(compiledDef.executionModule()).execute(parsedPgm, depth).k();
            return kResult;
        } finally {
            requestScope.exit();
        }
    }

    public Rewriter getRewriter() {
        requestScope.enter();
        rewriter = injector.getInstance(InitializeRewriter.class).apply(compiledDef.executionModule());
        requestScope.exit();
        return rewriter;
    }


    public Module getUnparsingModule() {
        return compiledDef.getExtensionModule(compiledDef.languageParsingModule());
    }

}
