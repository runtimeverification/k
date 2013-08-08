package org.kframework.backend.pdmc.pda;

import junit.framework.Assert;
import org.junit.Test;

/**
 * @author Traian
 */
public class RuleTest {
    @Test
    public void testOf() throws Exception {
        Rule<String, String> rule = Rule.<String,String>of("<a,b> => <c>" );
        Assert.assertEquals(Configuration.<String,String>of("<a,b>").getHead(), rule.getHead());
        Assert.assertEquals(Configuration.<String,String>of("<c>"), rule.endConfiguration());

    }
}
