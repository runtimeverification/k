package org.kframework.kore;

import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;

import org.apache.commons.io.FileUtils;
import org.junit.Rule;
import org.junit.Test;
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

import com.google.inject.util.Providers;

abstract class SDFCompilerTest extends BaseTestCase {

    @Rule
    public TestName name = new TestName();

    private static final String ROOT = "src/test/resources/sdf-compiler/";

    public Definition parse(String definitionText, String mainModule)
            throws IOException {
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

        FileUtil fileUtil = new FileUtil(tempDir.toFile(),
                Providers.of(definitionDir), definitionDir,
                Providers.of(kompiledDir), globalOptions, kem);

        context.files = fileUtil;

        String path = new File("../k-distribution/target/release/k/lib/native/")
                .getAbsolutePath() + "/" + OS.current() + "/";

        String nativeSDF2TableExecutable = path
                + OS.current().getNativeExecutable("sdf2table");

        Sdf2Table sdf2Table = new Sdf2Table(Providers.of(new ProcessBuilder()),
                nativeSDF2TableExecutable);

        File file = File.createTempFile("test", ".k");
        fileUtil.save(file, definitionText);

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

        BinaryLoader binaryLoader = mock(BinaryLoader.class);

        Definition parsedKIL = new DefinitionLoader(
                new Stopwatch(globalOptions), binaryLoader, kem,
                new OuterParser(globalOptions, false, null, fileUtil, kem),
                false, fileUtil, sdf2Table).parseDefinition(file, mainModule,
                context);

        return parsedKIL;
    }

}
