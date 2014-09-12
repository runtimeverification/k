// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import junit.framework.Assert;
import org.junit.Test;

/**
 * @author Traian
 */
public class GappaServerIT {
    @Test
    public void testProve1() throws Exception {
        boolean result = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertTrue(result);
    }

    @Test
    public void testProve2() throws Exception {
        boolean bytes;
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertTrue(bytes);
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertTrue(bytes);
    }

    @Test
    public void testProve3() throws Exception {
        boolean bytes;
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertTrue(bytes);
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [-2,-1] }");
        Assert.assertFalse(bytes);
        bytes = GappaServer.prove("{ x in [0,1] -> float<ieee_32,ne>(x * float<ieee_32,ne>(1 - x)) in [0,1] }");
        Assert.assertTrue(bytes);
    }
}
