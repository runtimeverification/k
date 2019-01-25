// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.kframework.backend.java.builtins.BuiltinListOperations;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.util.Subsorts;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class BuiltinListTest {

    @Mock
    GlobalContext globalContext;
    @Mock
    Definition definition;
    @Mock
    Subsorts subsorts;

    @Before
    public void setUp() {
    }

    @Test
    public void testListRange() throws Exception {
        BuiltinList baseBuiltinList = (BuiltinList) BuiltinListOperations.range(
                BuiltinList.builder(Sort.LIST, null, null, globalContext)
                        .addAll(IntToken.of(0), new Variable("L", Sort.LIST), IntToken.of(9), IntToken.of(10))
                        .build(),
                IntToken.of(1),
                IntToken.of(1),
                null);

        BuiltinList builtinList = (BuiltinList) BuiltinListOperations.range(
                BuiltinList.builder(Sort.LIST, null, null, globalContext)
                        .addAll(IntToken.of(0), IntToken.of(1))
                        .addAll(baseBuiltinList.children)
                        .addAll(IntToken.of(9), IntToken.of(10)).build(),
                IntToken.of(2),
                IntToken.of(1),
                null);

        Assert.assertEquals(builtinList.children, ImmutableList.of(new Variable("L", Sort.LIST), IntToken.of(9), IntToken.of(9)));
    }
}
