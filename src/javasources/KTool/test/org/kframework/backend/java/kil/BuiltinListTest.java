// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.util.KSorts;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import java.util.ArrayList;


public class BuiltinListTest {

    @Test
    public void testOf() throws Exception {
        BuiltinList baseBuiltinList = BuiltinList.of(
                new Variable("L", KSorts.LIST),
                1,
                1,
                new ArrayList<>(ImmutableList.<Term>of(IntToken.of(0))),
                new ArrayList<>(ImmutableList.<Term>of(IntToken.of(9), IntToken.of(10))));
        BuiltinList builtinList = BuiltinList.of(
                baseBuiltinList,
                2,
                1,
                new ArrayList<>(ImmutableList.<Term>of(IntToken.of(0), IntToken.of(1))),
                new ArrayList<>(ImmutableList.<Term>of(IntToken.of(9), IntToken.of(10))));

        Assert.assertEquals(builtinList.elementsLeft().size(), 2);
        Assert.assertEquals(builtinList.removeLeft(), 2);
        Assert.assertEquals(builtinList.elementsRight().size(), 3);
        Assert.assertEquals(builtinList.removeRight(), 1);
    }
}
