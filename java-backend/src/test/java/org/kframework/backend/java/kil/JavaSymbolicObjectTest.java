// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.Sets;
import org.junit.Before;
import org.junit.Test;
import org.kframework.kil.Attributes;
import org.kframework.utils.BaseTestCase;
import org.mockito.Mock;

import java.util.Collections;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

public class JavaSymbolicObjectTest extends BaseTestCase {

    @Mock
    Definition definition;

    @Before
    public void setUp() {
        when(definition.signaturesOf("foo")).thenReturn(Collections.emptySet());
        when(definition.allSorts()).thenReturn(Collections.singleton(Sort.of("Foo")));
        when(definition.kLabelAttributesOf("foo")).thenReturn(new Attributes());
    }

    @Test
    public void testVariableSet() {
        Variable v1 = new Variable("foo", Sort.of("bar"));
        assertEquals(Collections.singleton(v1), v1.variableSet());
        assertEquals(Collections.singleton(v1), v1.variableSet);

        KItem k1 = new KItem(KLabelConstant.of("foo", definition), KList.EMPTY, Sort.of("bar"), true);
        assertEquals(Collections.emptySet(), k1.variableSet());
        assertEquals(Collections.emptySet(), k1.variableSet);
        assertEquals(Collections.emptySet(), k1.kLabel().variableSet);
        assertEquals(Collections.emptySet(), k1.kList().variableSet);

        Variable v2 = new Variable("bar", Sort.of("baz"));
        KItem k2 = new KItem(KLabelConstant.of("foo", definition), v2, Sort.of("bar"), true);
        assertEquals(Collections.singleton(v2), k2.variableSet());
        assertEquals(Collections.singleton(v2), k2.variableSet);
        assertEquals(Collections.emptySet(), k2.kLabel().variableSet);
        assertEquals(Collections.singleton(v2), k2.kList().variableSet);

        Variable v3 = new Variable("baz", Sort.of("baz"));
        KList list = (KList) KList.concatenate(v3, k2);
        KItem k3 = new KItem(KLabelConstant.of("foo", definition), list, Sort.of("bar"), true);
        assertEquals(Sets.newHashSet(v2, v3), k3.variableSet());
        assertEquals(Sets.newHashSet(v2, v3), k3.variableSet);
        assertEquals(Collections.emptySet(), k3.kLabel().variableSet);
        assertSame(list, k3.kList());
        assertEquals(Sets.newHashSet(v2, v3), list.variableSet);
        assertSame(v3, list.get(0));
        assertSame(k2, list.get(1));
        assertEquals(Collections.singleton(v3), v3.variableSet);
        assertEquals(Collections.singleton(v2), k2.variableSet);
        assertEquals(Collections.emptySet(), k2.kLabel().variableSet);
        assertEquals(Collections.singleton(v2), k2.kList().variableSet);
    }

    @Test
    public void testIsNormal() {
        Variable v1 = new Variable("foo", Sort.of("bar"));
        assertTrue(v1.isNormal());

        KItem k1 = new KItem(KLabelConstant.of("foo", definition), KList.EMPTY, Sort.of("bar"), true);
        assertTrue(k1.isNormal());
        assertTrue(k1.kLabel().isNormal());
        assertTrue(k1.kList().isNormal());

        KItem k2 = new KItem(KLabelConstant.of("isFoo", definition), KList.EMPTY, Sort.of("bar"), true);
        assertFalse(k2.isNormal());
        assertTrue(k2.kLabel().isNormal());
        assertTrue(k2.kList().isNormal());

        KList list = (KList) KList.concatenate(k1, k2);
        KItem k3 = new KItem(KLabelConstant.of("foo", definition), list, Sort.of("bar"), true);
        assertFalse(k3.isNormal());
        assertTrue(k3.kLabel().isNormal());
        assertSame(list, k3.kList());
        assertFalse(list.isNormal());
        assertSame(k1, list.get(0));
        assertSame(k2, list.get(1));
        assertTrue(k1.isNormal());
        assertTrue(k1.kLabel().isNormal());
        assertTrue(k1.kList().isNormal());
        assertFalse(k2.isNormal());
        assertTrue(k2.kLabel().isNormal());
        assertTrue(k2.kList().isNormal());
    }
}
