package org.kframework.backend.java.util;

import junit.framework.Assert;
import org.junit.Test;

/**
 * @author Traian
 */
public class GappaServerTest {
    @Test
    public void testProve1() throws Exception {
        byte[] bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertEquals("OK", new String(bytes));
    }

    @Test
    public void testProve2() throws Exception {
        byte[] bytes;
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertEquals("OK", new String(bytes));
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertEquals("OK", new String(bytes));
    }

    @Test
    public void testProve3() throws Exception {
        byte[] bytes;
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertEquals("OK", new String(bytes));
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [-2,-1] }");
        Assert.assertEquals("FAIL", new String(bytes));
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertEquals("OK", new String(bytes));
    }
}
