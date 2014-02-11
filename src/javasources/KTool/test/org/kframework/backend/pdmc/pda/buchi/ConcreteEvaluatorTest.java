package org.kframework.backend.pdmc.pda.buchi;

import org.junit.Assert;
import org.junit.Test;

/**
 * Created by Traian on 04.02.2014.
 */
public class ConcreteEvaluatorTest {
    @Test
    public void testOf() throws Exception {
        String concreteEvaluatorString = ""
                + "<p,a> |= x y z;\n"
                + "<q,b> |= m x z;\n"
                + "<r,a> |= x m;\n"
                + "";
        ConcreteEvaluator<String, String> evaluator = ConcreteEvaluator.of(concreteEvaluatorString);
        Assert.assertEquals(concreteEvaluatorString.length(), evaluator.toString().length());

    }
}
