// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.junit.Assert;
import org.junit.Test;
import org.kframework.backend.java.builtins.BuiltinListOperations;
import org.kframework.backend.java.builtins.BuiltinMapOperations;
import org.kframework.backend.java.builtins.IntToken;
import org.mockito.Mock;


public class BuiltinMapTest {

    @Mock
    TermContext termContext;

    @Test
    public void testMapUpdate1() throws Exception {
        BuiltinMap.Builder builder = BuiltinMap.builder();
        builder.put(IntToken.of(0), IntToken.of(0));
        builder.put(IntToken.of(1), IntToken.of(0));
        BuiltinMap builtinMap = (BuiltinMap) builder.build();


        builder = BuiltinMap.builder();
        builder.put(IntToken.of(1), IntToken.of(1));
        builder.put(IntToken.of(2), IntToken.of(1));
        BuiltinMap updateMap = (BuiltinMap) builder.build();

        BuiltinMap resultMap = (BuiltinMap) BuiltinMapOperations.updateAll(
                builtinMap,
                updateMap,
                termContext);

        Assert.assertEquals(true, resultMap.isConcreteCollection());
        Assert.assertEquals(3, resultMap.concreteSize());
        Assert.assertEquals(IntToken.of(0), resultMap.getEntries().get(IntToken.of(0)));
        Assert.assertEquals(IntToken.of(1), resultMap.getEntries().get(IntToken.of(1)));
        Assert.assertEquals(IntToken.of(1), resultMap.getEntries().get(IntToken.of(2)));
    }

    @Test
    public void testMapUpdate2() throws Exception {
        BuiltinMap.Builder builder = BuiltinMap.builder();
        builder.put(IntToken.of(0), IntToken.of(0));
        builder.put(IntToken.of(1), IntToken.of(0));
        builder.put(IntToken.of(2), IntToken.of(0));
        builder.concatenate(new Variable("M", Sort.MAP));
        BuiltinMap builtinMap = (BuiltinMap) builder.build();


        builder = BuiltinMap.builder();
        builder.put(IntToken.of(0), IntToken.of(1));
        builder.put(IntToken.of(1), IntToken.of(1));
        BuiltinMap updateMap = (BuiltinMap) builder.build();

        BuiltinMap resultMap = (BuiltinMap) BuiltinMapOperations.updateAll(
                builtinMap,
                updateMap,
                termContext);

        Assert.assertEquals(new Variable("M", Sort.MAP), builtinMap.frame());
        Assert.assertEquals(3, resultMap.concreteSize());
        Assert.assertEquals(IntToken.of(1), resultMap.getEntries().get(IntToken.of(0)));
        Assert.assertEquals(IntToken.of(1), resultMap.getEntries().get(IntToken.of(1)));
        Assert.assertEquals(IntToken.of(0), resultMap.getEntries().get(IntToken.of(2)));
    }

    @Test
    public void testMapUpdate3() throws Exception {
        BuiltinMap.Builder builder = BuiltinMap.builder();
        builder.put(IntToken.of(0), IntToken.of(0));
        builder.put(IntToken.of(1), IntToken.of(0));
        builder.concatenate(new Variable("M", Sort.MAP));
        BuiltinMap builtinMap = (BuiltinMap) builder.build();


        builder = BuiltinMap.builder();
        builder.put(IntToken.of(0), IntToken.of(1));
        builder.put(IntToken.of(1), IntToken.of(1));
        builder.put(IntToken.of(2), IntToken.of(1));
        BuiltinMap updateMap = (BuiltinMap) builder.build();

        Term resultMap = BuiltinMapOperations.updateAll(
                builtinMap,
                updateMap,
                termContext);

        Assert.assertEquals(null, resultMap);
    }

}
