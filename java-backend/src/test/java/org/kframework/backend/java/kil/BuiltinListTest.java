// Copyright (c) 2014-2016 K Team. All Rights Reserved.

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
        BuiltinList baseBuiltinList = (BuiltinList) BuiltinListOperations.range(
                BuiltinList.builder(Sort.LIST, null, null, termContext.global())
                        .addAll(IntToken.of(0), new Variable("L", Sort.LIST), IntToken.of(9), IntToken.of(10))
                        .build(),
                IntToken.of(1),
                IntToken.of(1),
                termContext);

        BuiltinList builtinList = (BuiltinList) BuiltinListOperations.range(
                BuiltinList.builder(Sort.LIST, null, null, termContext.global())
                        .addAll(IntToken.of(0), IntToken.of(1))
                        .addAll(baseBuiltinList.children)
                        .addAll(IntToken.of(9), IntToken.of(10)).build(),
                IntToken.of(2),
                IntToken.of(1),
                termContext);

        Assert.assertEquals(builtinList.children, ImmutableList.of(new Variable("L", Sort.LIST), IntToken.of(9), IntToken.of(9)));
    }
}
