// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import com.beust.jcommander.JCommander;

public class DefinitionLoadingOptionsTest {

    @Test
    public void testReadDefinition() throws IOException {
        DefinitionLoadingOptions options = new DefinitionLoadingOptions();
        new JCommander(options, "--directory", "src/test/resources");
        assertEquals(new File("src/test/resources/test-kompiled").getCanonicalPath(), options.definition().getCanonicalPath());
        assertTrue(options.definition().exists());
        assertTrue(options.definition().isDirectory());
    }
}
