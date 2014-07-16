// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils;

import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;

import com.google.common.collect.Sets;

public class PosetTest {

    private Poset poset;

    @Before
    public void setUp() {
        poset = new Poset();
        poset.addRelation("Top", "A0");
        poset.addRelation("Top", "A1");
        poset.addRelation("Top", "A2");
        poset.addRelation("A0", "B0");
        poset.addRelation("A1", "B0");
        poset.addRelation("A2", "B0");
        poset.addRelation("A0", "B1");
        poset.addRelation("A1", "B1");
        poset.addRelation("A2", "B1");
        poset.addRelation("B0", "Bot");
        poset.addRelation("B1", "Bot");
        poset.transitiveClosure();
    }

    @Test
    public void testGetMaximalLowerBounds() throws Exception {
        Assert.assertEquals(Sets.newHashSet("B0", "B1"),
                poset.getMaximalLowerBounds(Sets.newHashSet("A0", "A1", "A2")));
    }

    @Test
    public void testGetMinimalUpperBounds() throws Exception {
        Assert.assertEquals(Sets.newHashSet("A0", "A1", "A2"),
                poset.getMinimalUpperBounds(Sets.newHashSet("B0", "B1")));
    }

    @Test
    public void testGetGLB() throws Exception {
        // multiple lower bounds, but no GLB
        Assert.assertNull(poset.getGLB(Sets.newHashSet("A0", "A1", "A2")));

        // create a GLB for A0, A1, and A2
        poset.addRelation("A0", "GLB");
        poset.addRelation("A1", "GLB");
        poset.addRelation("A2", "GLB");
        poset.addRelation("GLB", "B0");
        poset.addRelation("GLB", "B1");
        poset.transitiveClosure();
        Assert.assertEquals("GLB", poset.getGLB(Sets.newHashSet("A0", "A1", "A2")));
    }

    @Test
    public void testGetLUB() throws Exception {
        // multiple upper bounds, but no LUB
        Assert.assertNull(poset.getLUB(Sets.newHashSet("B0", "B1")));

        // create a LUB for B0, B1
        poset.addRelation("A0", "LUB");
        poset.addRelation("A1", "LUB");
        poset.addRelation("A2", "LUB");
        poset.addRelation("LUB", "B0");
        poset.addRelation("LUB", "B1");
        poset.transitiveClosure();
        Assert.assertEquals("LUB", poset.getLUB(Sets.newHashSet("B0", "B1")));
    }
}
