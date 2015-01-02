// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.unparser;

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
        context.krunOptions = new KRunOptions();
    }

    /**
     * Regression test for an ArrayOutOfBoundsException on labels with multiple trailing underscores,
     */
    @Test
    public void testTrailingUnderscores() {
        UnparserFilter v = new UnparserFilter(context);
        KApp t = KApp.of(KLabelConstant.of("'__"), Variable.getAnonVar(Sort.K), Variable.getAnonVar(Sort.K));
        v.visit(t, null);
        v.getResult();
    }

}
