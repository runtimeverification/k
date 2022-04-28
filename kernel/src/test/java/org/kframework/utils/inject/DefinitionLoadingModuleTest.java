// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;

import org.junit.Test;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.options.DefinitionLoadingOptions;

import com.beust.jcommander.JCommander;

public class DefinitionLoadingModuleTest {

    @Test
    public void testReadDefinition() throws IOException {
        DefinitionLoadingOptions options = new DefinitionLoadingOptions();
        new JCommander(options, "--directory", "src/test/resources");
        DefinitionLoadingModule module = new DefinitionLoadingModule();
        File defDir = module.directory(options, new File("."));
        assertEquals(new File("src/test/resources").getCanonicalFile(), defDir.getCanonicalFile());
        File kompiledDir = module.definition(defDir);
        assertEquals(new File("src/test/resources/test-kompiled").getCanonicalFile(), kompiledDir.getCanonicalFile());
        assertTrue(kompiledDir.exists());
        assertTrue(kompiledDir.isDirectory());
    }
}
