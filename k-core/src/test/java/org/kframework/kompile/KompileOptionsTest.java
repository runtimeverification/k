// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

import java.io.File;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.kframework.backend.Backends;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.invocation.InvocationOnMock;
import org.mockito.runners.MockitoJUnitRunner;
import org.mockito.stubbing.Answer;

import com.beust.jcommander.JCommander;

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
        options.setFiles(files);
        when(files.resolveWorkingDirectory(Matchers.anyString())).thenAnswer(new Answer<File>() {
            @Override
            public File answer(InvocationOnMock invocation) throws Throwable {
                return new File((String) invocation.getArguments()[0]);
            }
        });
    }

    private void parse(String... args) {
        new JCommander(options, args);
        options.mainDefinitionFile();
        options.mainModule();
        options.docStyle();
        options.syntaxModule();
    }

    @Test(expected=KExceptionManager.KEMException.class)
    public void testNoDefinition() throws Exception {
        parse();
    }

    @Test
    public void testHtmlDocStyle() {
        parse("--backend", "html", "foo.k");
        assertEquals(Backends.HTML, options.backend);
        assertEquals("k-definition.css", options.docStyle());
    }

    @Test
    public void testDocStylePlus() {
        parse("--doc-style", "+foo", "foo.k");
        assertEquals("poster,style=bubble,foo", options.docStyle());
    }

    @Test
    public void testDefaultModuleName() {
        parse("foo.k");
        assertEquals("FOO", options.mainModule());
    }

    @Test
    public void testDefaultSyntaxModuleName() {
        parse("--main-module", "BAR", "foo.k");
        assertEquals("BAR-SYNTAX", options.syntaxModule());
    }

    @Test
    public void testTransitionSpaceSeparator() {
        parse("--transition", "foo bar", "foo.k");
        assertEquals(2, options.transition.size());
        assertTrue(options.transition.contains("foo"));
        assertTrue(options.transition.contains("bar"));
    }
}
