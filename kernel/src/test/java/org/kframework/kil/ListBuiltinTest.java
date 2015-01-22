// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;

import org.junit.Before;
import org.junit.Test;

public class ListBuiltinTest {

    DataStructureSort listSort;

    @Before
    public void setUp() {
        listSort = new DataStructureSort(
                "List", Sort.LIST, "'_List_", "'ListItem", "'.List", new HashMap<String, String>());
    }

    @Test
    public void testListBuiltinAsBaseTerm() {
        ListBuiltin left = ListBuiltin.of(listSort, Collections.<Term>emptyList(),
                Collections.<Term>emptyList(),
                Arrays.<Term>asList(KApp.of("zero")));
        ListBuiltin right = ListBuiltin.of(listSort, Collections.<Term>emptyList(),
                Arrays.<Term>asList(KApp.of("two"), KApp.of("three"), KApp.of("four")),
                Collections.<Term>emptyList());
        ListBuiltin right2 = ListBuiltin.of(listSort, Collections.<Term>emptyList(),
                Arrays.<Term>asList(KApp.of("five")),
                Collections.<Term>emptyList());
        ListBuiltin outer = ListBuiltin.of(listSort, Arrays.asList(left, new Variable("one", Sort.LIST), right),
                Collections.<Term>emptyList(),
                Arrays.<Term>asList(KApp.of("five")));
        assertEquals(Arrays.asList(KApp.of("zero")), outer.elementsLeft());
        assertEquals(Arrays.asList(KApp.of("two"), KApp.of("three"), KApp.of("four"),
                KApp.of("five")), outer.elementsRight());
        assertEquals(new Variable("one", Sort.LIST), outer.viewBase());

        ListBuiltin outer2 = (ListBuiltin)DataStructureBuiltin.of(listSort,
                left, new Variable("one", Sort.LIST), right, right2);
        assertEquals(Arrays.asList(KApp.of("zero")), outer2.elementsLeft());
        assertEquals(Arrays.asList(KApp.of("two"), KApp.of("three"), KApp.of("four"),
                KApp.of("five")), outer2.elementsRight());
        assertEquals(new Variable("one", Sort.LIST), outer2.viewBase());
    }

    @Test
    public void testElementsRightNormalization() {
        ListBuiltin b = ListBuiltin.of(listSort, Collections.<Term>emptyList(), Arrays.<Term>asList(KApp.of("zero")),
                Arrays.<Term>asList(KApp.of("five")));
        assertEquals(Arrays.asList(KApp.of("zero"), KApp.of("five")), b.elementsLeft());
        assertEquals(Collections.<Term>emptyList(), b.elementsRight());
        assertEquals(Collections.<Term>emptyList(), b.baseTerms());
    }

    @Test
    public void testBaseTermWithElements() {
        ListBuiltin inner = ListBuiltin.of(listSort, Arrays.<Term>asList(new Variable("v", Sort.LIST)),
                Arrays.<Term>asList(KApp.of("k")), Collections.<Term>emptyList());
        ListBuiltin outer = (ListBuiltin)DataStructureBuiltin.of(listSort, inner, inner);
        assertEquals(Arrays.<Term>asList(KApp.of("k")), outer.elementsLeft());
        assertEquals(Collections.<Term>emptyList(), outer.elementsRight());
        assertEquals(Arrays.<Term>asList(new Variable("v", Sort.LIST),
                ListBuiltin.element(listSort, KApp.of("k")), new Variable("v", Sort.LIST)), outer.baseTerms());
    }

    @Test
    public void testMultipleVariables() {
        ListBuiltin inner = ListBuiltin.of(listSort, Arrays.<Term>asList(new Variable("L", Sort.LIST)),
                Arrays.<Term>asList(KApp.of("k")), Arrays.<Term>asList(KApp.of("k")));
        ListBuiltin outer = (ListBuiltin) DataStructureBuiltin.of(listSort, inner, new Variable("L", Sort.LIST));
        assertEquals(Arrays.<Term>asList(KApp.of("k")), outer.elementsLeft());
        assertEquals(Arrays.asList(new Variable("L", Sort.LIST), DataStructureBuiltin.element(listSort, KApp.of("k")), new Variable("L", Sort.LIST)), outer.baseTerms());
        assertEquals(Collections.<Term>emptyList(), outer.elementsRight());
    }
}
