// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import com.google.inject.util.Providers;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.kompile.KompileOptions.Experimental;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.DefinitionLoader;
import org.kframework.parser.generator.OuterParser;
import org.kframework.parser.utils.Sdf2Table;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.OS;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;

import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public abstract class SDFCompilerTest extends BaseTestCase {

    @Rule
    public TestName name = new TestName();

    @SuppressWarnings("deprecation")
    public BaseTest.DefinitionWithContext parse(File definitionFile, String mainModule, boolean autoinclude) throws IOException {
        // Not a complete fix, but seems to reduce sporadic test failures
        synchronized (SDFCompilerTest.class) {
            return unsafeParse(definitionFile, mainModule, autoinclude);
        }
    }

    // Not threadsafe, SDF uses too much static state.
    private BaseTest.DefinitionWithContext unsafeParse(File definitionFile, String mainModule, boolean autoinclude) throws IOException {
        // KExceptionManager kem = new KExceptionManager(new GlobalOptions());

        GlobalOptions globalOptions = new GlobalOptions();
        // GlobalSettings.kem = kem;
        context = new Context();
        context.globalOptions = globalOptions;

        Path testDir = Files.createTempDirectory("test");
        Path tempDir = Files.createTempDirectory("temp");
        File definitionDir = new File(testDir.toAbsolutePath().toString());
        File kompiledDir = new File(definitionDir, "test-kompiled");

        context.globalOptions = globalOptions;

        FileUtil fileUtil = new FileUtil(tempDir.toFile(), Providers.of(definitionDir),
                definitionDir, Providers.of(kompiledDir), globalOptions, System.getenv());

        String path = new File(JarInfo.getKBase() + "/lib/native/").getAbsolutePath()
                + "/" + OS.current().name().toLowerCase() + "/";

        String nativeSDF2TableExecutable = path + OS.current().getNativeExecutable("sdf2table");

        nativeSDF2TableExecutable = nativeSDF2TableExecutable.replace("k-distribution/k-distribution", "k-distribution");

        Sdf2Table sdf2Table = new Sdf2Table(Providers.of(new ProcessBuilder()),
                nativeSDF2TableExecutable);

        KompileOptions kompileOptions = mock(KompileOptions.class);
        when(kompileOptions.mainModule()).thenReturn(mainModule);
        kompileOptions.global = globalOptions;
        // kompileOptions.backend = Backends.SYMBOLIC;
        // kompileOptions.experimental = new Experimental();;
        kompileOptions.transition = new ArrayList<String>();
        kompileOptions.supercool = new ArrayList<String>();
        kompileOptions.superheat = new ArrayList<String>();

        context.kompileOptions = kompileOptions;
        kompileOptions.experimental = new Experimental();
        kompileOptions.experimental.legacyKast = false;

        BinaryLoader binaryLoader = new BinaryLoader(kem);

        Definition parsedKIL = new DefinitionLoader(new Stopwatch(globalOptions), binaryLoader,
                kem, new OuterParser(globalOptions, autoinclude, "autoinclude-java.k", fileUtil, kem),
                autoinclude, fileUtil, sdf2Table).parseDefinition(definitionFile, mainModule, context);

        return new BaseTest.DefinitionWithContext(parsedKIL, context);
    }

}
