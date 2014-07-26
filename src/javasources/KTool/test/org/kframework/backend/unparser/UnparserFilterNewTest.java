// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.backend.unparser;

import java.util.Map;

import org.junit.Before;
import org.junit.Test;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Sort;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions;
import org.mockito.Mockito;

public class UnparserFilterNewTest {
    Context context;

    @SuppressWarnings("unchecked")
    @Before
    public void setup() {
        context = Mockito.mock(Context.class);
        context.canonicalBracketForSort = Mockito.mock(Map.class);
        context.krunOptions = new KRunOptions();
    }

    /**
     * Regression test for an ArrayOutOfBoundsException on labels with multiple trailing underscores,
     */
    @Test
    public void testTrailingUnderscores() {
        UnparserFilterNew v = new UnparserFilterNew(context);
        KApp t = KApp.of(KLabelConstant.of("'__", context), Variable.getFreshVar(Sort.K), Variable.getFreshVar(Sort.K));
        v.visit(t, null);
        v.getResult();
    }

}
