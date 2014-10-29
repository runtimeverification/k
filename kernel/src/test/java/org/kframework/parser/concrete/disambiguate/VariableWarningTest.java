// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import static org.mockito.Mockito.*;

import org.junit.Before;
import org.junit.Test;
import org.kframework.kil.KSequence;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.mockito.ArgumentMatcher;

public class VariableWarningTest extends BaseTestCase {

    @Before
    public void setUp() {
        context = new Context();
        context.globalOptions = new GlobalOptions();

    }

    @Test
    public void testWarnings() throws ParseFailedException {
        Rule r = new Rule();
        Variable v1 = new Variable("A", Sort.K);
        v1.setUserTyped(false);
        Variable v2 = new Variable("A", Sort.K);
        v2.setUserTyped(false);
        Variable v3 = new Variable("B", Sort.K);
        v3.setUserTyped(true);
        Variable v4 = new Variable("B", Sort.K);
        v4.setUserTyped(false);
        KSequence ks = new KSequence();
        ks.getContents().add(v1);
        ks.getContents().add(v2);
        ks.getContents().add(v3);
        ks.getContents().add(v4);
        r.setBody(ks);

        new VariableTypeInferenceFilter(context, kem).visitNode(r);
        verify(kem).register(argThat(new ArgumentMatcher<KException>() {
            @Override
            public boolean matches(Object argument) {
                return ((KException)argument).getType() == ExceptionType.HIDDENWARNING;
            }
        }));
    }
}
