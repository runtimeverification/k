// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.beust.jcommander.JCommander;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.kframework.backend.Backends;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.invocation.InvocationOnMock;
import org.mockito.runners.MockitoJUnitRunner;
import org.mockito.stubbing.Answer;

import java.io.File;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

@RunWith(MockitoJUnitRunner.class)
public class KompileOptionsTest {

    private KompileOptions options;

    @Mock
    KExceptionManager kem;

    @Mock
    FileUtil files;

    @Before
    public void setUp() {
        options = new KompileOptions();
        when(files.resolveWorkingDirectory(Matchers.anyString())).thenAnswer(new Answer<File>() {
            @Override
            public File answer(InvocationOnMock invocation) throws Throwable {
                return new File((String) invocation.getArguments()[0]);
            }
        });
    }

    private void parse(String... args) {
        new JCommander(options, args);
        options.outerParsing.mainDefinitionFile(files);
        options.mainModule(files);
        options.syntaxModule(files);
    }

    @Test(expected=KEMException.class)
    public void testNoDefinition() throws Exception {
        parse();
    }

    @Test
    public void testDefaultModuleName() {
        parse("foo.k");
        assertEquals("FOO", options.mainModule(files));
    }

    @Test
    public void testDefaultSyntaxModuleName() {
        parse("--main-module", "BAR", "foo.k");
        assertEquals("BAR-SYNTAX", options.syntaxModule(files));
    }

    @Test
    public void testTransitionSpaceSeparator() {
        parse("--transition", "foo bar", "foo.k");
        assertEquals(2, options.transition.size());
        assertTrue(options.transition.contains("foo"));
        assertTrue(options.transition.contains("bar"));
    }
}
