// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.IntToken;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableList;


public class BuiltinListTest {

    @Test
    public void testOf() throws Exception {
        BuiltinList.Builder builder = BuiltinList.builder();
        builder.addItem(IntToken.of(0));
        builder.concatenate(new Variable("L", Sort.LIST));
        builder.addItems(ImmutableList.<Term>of(IntToken.of(9), IntToken.of(10)));
        BuiltinList baseBuiltinList = (BuiltinList) new ListUpdate(builder.build(), 1, 1).evaluateUpdate();

        builder = BuiltinList.builder();
        builder.addItems(ImmutableList.<Term>of(IntToken.of(0), IntToken.of(1)));
        builder.concatenate(baseBuiltinList);
        builder.addItems(ImmutableList.<Term>of(IntToken.of(9), IntToken.of(10)));
        BuiltinList builtinList = (BuiltinList) new ListUpdate(builder.build(), 2, 1).evaluateUpdate();

        Assert.assertEquals(new Variable("L", Sort.LIST), builtinList.frame());
        Assert.assertEquals(2, builtinList.concreteSize());
        Assert.assertEquals(IntToken.of(9), builtinList.get(-1));
        Assert.assertEquals(IntToken.of(9), builtinList.get(-2));
    }
}
