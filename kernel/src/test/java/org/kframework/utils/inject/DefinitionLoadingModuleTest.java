// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.beust.jcommander.JCommander;
import org.junit.Test;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.OutputDirectoryOptions;

import java.io.File;
import java.io.IOException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class DefinitionLoadingModuleTest {

    @Test
    public void testReadDefinition() throws IOException {
        DefinitionLoadingOptions options = new DefinitionLoadingOptions();
        new JCommander(options, "--directory", "src/test/resources");
        DefinitionLoadingModule module = new DefinitionLoadingModule();
        File kompiledDir = module.directory(options, new File("."), System.getenv());
        assertEquals(new File("src/test/resources/test-kompiled").getCanonicalFile(), kompiledDir.getCanonicalFile());
        assertTrue(kompiledDir.exists());
        assertTrue(kompiledDir.isDirectory());
    }

    @Test
    public void testReadDefinition2() throws IOException {
        DefinitionLoadingOptions options = new DefinitionLoadingOptions();
        new JCommander(options, "--definition", "src/test/resources/test-kompiled");
        DefinitionLoadingModule module = new DefinitionLoadingModule();
        File kompiledDir = module.directory(options, new File("."), System.getenv());
        assertEquals(new File("src/test/resources/test-kompiled").getCanonicalFile(), kompiledDir.getCanonicalFile());
        assertTrue(kompiledDir.exists());
        assertTrue(kompiledDir.isDirectory());
    }

    @Test(expected = KEMException.class)
    public void testReadDefinition3() throws KEMException {
        DefinitionLoadingOptions options = new DefinitionLoadingOptions();
        new JCommander(options, "--directory", "src/test/resources/test-kompiled");
        DefinitionLoadingModule module = new DefinitionLoadingModule();
        File defDir = module.directory(options, new File("."), System.getenv());
    }

    @Test
    public void testSaveDefinition() throws IOException, KEMException {
        OutputDirectoryOptions options = new OutputDirectoryOptions();
        new JCommander(options, "-o", "src/test/resources/test-kompiled");

        FileUtil fu = new FileUtil(null, new File("."), new File("src/test/resources/test-kompiled"), null, null);
        File abcd = fu.resolveDefinitionDirectory("abacd");
        System.out.println(abcd);
    }
}
