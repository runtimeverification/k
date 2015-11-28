// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.kframework.backend.java.builtins.BuiltinListOperations;
import org.kframework.backend.java.builtins.IntToken;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

@RunWith(MockitoJUnitRunner.class)
public class BuiltinListTest {

    @Mock
    TermContext termContext;

    @Test
    public void testListRange() throws Exception {
        BuiltinList.Builder builder = BuiltinList.builder(termContext.global());
        builder.addItem(IntToken.of(0));
        builder.concatenate(new Variable("L", Sort.LIST));
        builder.addItems(ImmutableList.<Term>of(IntToken.of(9), IntToken.of(10)));
        BuiltinList baseBuiltinList = (BuiltinList) BuiltinListOperations.range(
                (BuiltinList) builder.build(),
                IntToken.of(1),
                IntToken.of(1),
                termContext);

        builder = BuiltinList.builder(termContext.global());
        builder.addItems(ImmutableList.<Term>of(IntToken.of(0), IntToken.of(1)));
        builder.concatenate(baseBuiltinList);
        builder.addItems(ImmutableList.<Term>of(IntToken.of(9), IntToken.of(10)));
        BuiltinList builtinList = (BuiltinList) BuiltinListOperations.range(
                (BuiltinList) builder.build(),
                IntToken.of(2),
                IntToken.of(1),
                termContext);

        Assert.assertEquals(new Variable("L", Sort.LIST), builtinList.frame());
        Assert.assertEquals(2, builtinList.concreteSize());
        Assert.assertEquals(IntToken.of(9), builtinList.get(-1));
        Assert.assertEquals(IntToken.of(9), builtinList.get(-2));
    }
}
