// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.krun.api.io.FileSystem;
import org.mockito.Mockito;

public class BuiltinIOOperationsTest {

    private TermContext context;
    private FileSystem fs;

    @Before
    public void setUp() throws Exception {
        context = Mockito.mock(TermContext.class);
        fs = Mockito.mock(FileSystem.class);

        Mockito.when(context.fileSystem()).thenReturn(fs);
    }

    @Test
    public void testOpen() throws Exception {
        StringToken path = StringToken.of("foo");
        StringToken mode = StringToken.of("r");

        Mockito.when(fs.open("foo", "r")).thenReturn(3L);

        Term res = new BuiltinIOOperationsImpl(null, fs, null, null, null).open(path, mode, context);
        Assert.assertTrue(res instanceof IntToken);
        Assert.assertEquals(3, ((IntToken)res).intValue());
    }
}
