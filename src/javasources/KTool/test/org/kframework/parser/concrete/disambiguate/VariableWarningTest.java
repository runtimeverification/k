// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import junit.framework.Assert;
import org.junit.Before;
import org.junit.Test;
import org.kframework.kil.KSequence;
import org.kframework.kil.KSorts;
import org.kframework.kil.Rule;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.general.GlobalSettings;

public class VariableWarningTest {

    GlobalOptions go = new GlobalOptions();
    Context context = new Context(go);
    @Before
    public void init() {
        go.initialize();
    }

    @Test
    public void testWarnings() throws ParseFailedException {
        Rule r = new Rule();
        Variable v1 = new Variable("A", KSorts.K);
        v1.setUserTyped(false);
        Variable v2 = new Variable("A", KSorts.K);
        v2.setUserTyped(false);
        Variable v3 = new Variable("B", KSorts.K);
        v3.setUserTyped(true);
        Variable v4 = new Variable("B", KSorts.K);
        v4.setUserTyped(false);
        KSequence ks = new KSequence();
        ks.getContents().add(v1);
        ks.getContents().add(v2);
        ks.getContents().add(v3);
        ks.getContents().add(v4);
        r.setBody(ks);

        new VariableTypeInferenceFilter(context).visitNode(r);
        Assert.assertEquals("Expected one warning from here.", 1, GlobalSettings.kem.getExceptions().size());
    }
}
