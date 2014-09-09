// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.kframework.backend.Backends;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;
import org.kframework.utils.general.GlobalSettings;
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import com.beust.jcommander.JCommander;

@RunWith(MockitoJUnitRunner.class)
public class KompileOptionsTest {

    private KompileOptions options;

    @Mock
    KExceptionManager kem;

    @Before
    public void setUp() {
        options = new KompileOptions();
        GlobalSettings.kem = kem;
        doThrow(KEMException.class).when(kem).registerCriticalError(Matchers.anyString());
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
