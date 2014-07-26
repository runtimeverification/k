// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.kframework.kil.DataStructureBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Production;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.Sort;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import com.google.common.collect.Maps;

@RunWith(MockitoJUnitRunner.class)
public class ToKAppTransformerTest {

    @Mock
    private Context context;

    private ToKAppTransformer transformer;

    private DataStructureSort mapSort;
    private DataStructureSort listSort;
    private DataStructureSort setSort;

    @Before
    public void setUp() {
        transformer = new ToKAppTransformer(context);
        mapSort = new DataStructureSort("Map", Sort.MAP, "'_Map_", "'_|->_", "'.Map", Maps.<String, String>newHashMap());
        listSort = new DataStructureSort("List", Sort.LIST, "'_List_", "'ListItem", "'.List", Maps.<String, String>newHashMap());
        setSort = new DataStructureSort("Set", Sort.SET, "'_Set_", "'SetItem", "'.Set", Maps.<String, String>newHashMap());
        when(context.dataStructureSortOf(Sort.MAP)).thenReturn(mapSort);
        when(context.dataStructureSortOf(Sort.LIST)).thenReturn(listSort);
        when(context.dataStructureSortOf(Sort.SET)).thenReturn(setSort);
        context.canonicalBracketForSort = Maps.newHashMap();
    }

    @Test
    public void testUnit() {
        MapBuiltin mapUnit = (MapBuiltin) DataStructureBuiltin.empty(mapSort);
        ListBuiltin listUnit = (ListBuiltin) DataStructureBuiltin.empty(listSort);
        SetBuiltin setUnit = (SetBuiltin) DataStructureBuiltin.empty(setSort);

        KApp mapKApp = (KApp) transformer.visitNode(mapUnit);
        KApp listKApp = (KApp) transformer.visitNode(listUnit);
        KApp setKApp = (KApp) transformer.visitNode(setUnit);

        assertEquals(KApp.of("'.Map"), mapKApp);
        assertEquals(KApp.of("'.List"), listKApp);
        assertEquals(KApp.of("'.Set"), setKApp);
    }

    @Test
    public void testElement() {
        MapBuiltin mapElement = (MapBuiltin) DataStructureBuiltin.element(mapSort, KSequence.EMPTY, KSequence.EMPTY);
        ListBuiltin listElement = (ListBuiltin) DataStructureBuiltin.element(listSort, KSequence.EMPTY);
        SetBuiltin setElement = (SetBuiltin) DataStructureBuiltin.element(setSort, KSequence.EMPTY);

        KApp mapKApp = (KApp) transformer.visitNode(mapElement);
        KApp listKApp = (KApp) transformer.visitNode(listElement);
        KApp setKApp = (KApp) transformer.visitNode(setElement);

        assertEquals(KApp.of("'_|->_", KSequence.EMPTY, KSequence.EMPTY), mapKApp);
        assertEquals(KApp.of("'ListItem", KSequence.EMPTY), listKApp);
        assertEquals(KApp.of("'SetItem", KSequence.EMPTY), setKApp);
    }

    @Test
    public void testConstructor() {
        MapBuiltin mapElement1 = (MapBuiltin) DataStructureBuiltin.element(mapSort, IntBuiltin.kAppOf(1), KSequence.EMPTY);
        MapBuiltin mapElement2 = (MapBuiltin) DataStructureBuiltin.element(mapSort, IntBuiltin.kAppOf(2), KSequence.EMPTY);
        ListBuiltin listElement = (ListBuiltin) DataStructureBuiltin.element(listSort, KSequence.EMPTY);
        SetBuiltin setElement1 = (SetBuiltin) DataStructureBuiltin.element(setSort, IntBuiltin.kAppOf(1));
        SetBuiltin setElement2 = (SetBuiltin) DataStructureBuiltin.element(setSort, IntBuiltin.kAppOf(2));

        MapBuiltin map = (MapBuiltin) DataStructureBuiltin.of(mapSort, mapElement1, mapElement2);
        ListBuiltin list = (ListBuiltin) DataStructureBuiltin.of(listSort, listElement, listElement);
        SetBuiltin set = (SetBuiltin) DataStructureBuiltin.of(setSort, setElement1, setElement2);

        KApp mapKApp = (KApp) transformer.visitNode(map);
        KApp listKApp = (KApp) transformer.visitNode(list);
        KApp setKApp = (KApp) transformer.visitNode(set);

        assertEquals(KApp.of("'_Map_", KApp.of("'_|->_", IntBuiltin.kAppOf(1), KSequence.EMPTY),
                KApp.of("'_|->_", IntBuiltin.kAppOf(2), KSequence.EMPTY)), mapKApp);
        assertEquals(KApp.of("'_List_", KApp.of("'ListItem", KSequence.EMPTY),
                KApp.of("'ListItem", KSequence.EMPTY)), listKApp);
        assertEquals(KApp.of("'_Set_", KApp.of("'SetItem", IntBuiltin.kAppOf(1)),
                KApp.of("'SetItem", IntBuiltin.kAppOf(2))), setKApp);

    }

    @Test
    public void testFrame() {
        MapBuiltin mapElement = (MapBuiltin) DataStructureBuiltin.element(mapSort, KSequence.EMPTY, KSequence.EMPTY);
        ListBuiltin listElement = (ListBuiltin) DataStructureBuiltin.element(listSort, KSequence.EMPTY);
        SetBuiltin setElement = (SetBuiltin) DataStructureBuiltin.element(setSort, KSequence.EMPTY);

        MapBuiltin map = (MapBuiltin) DataStructureBuiltin.of(mapSort, mapElement, new Variable("M", Sort.MAP));
        ListBuiltin list = (ListBuiltin) DataStructureBuiltin.of(listSort, listElement, new Variable("L", Sort.LIST));
        SetBuiltin set = (SetBuiltin) DataStructureBuiltin.of(setSort, setElement, new Variable("S", Sort.SET));

        KApp mapKApp = (KApp) transformer.visitNode(map);
        KApp listKApp = (KApp) transformer.visitNode(list);
        KApp setKApp = (KApp) transformer.visitNode(set);

        assertEquals(KApp.of("'_Map_", KApp.of("'_|->_", KSequence.EMPTY, KSequence.EMPTY),
                new Variable("M", Sort.MAP)), mapKApp);
        assertEquals(KApp.of("'_List_", KApp.of("'ListItem", KSequence.EMPTY),
                new Variable("L", Sort.LIST)), listKApp);
        assertEquals(KApp.of("'_Set_", KApp.of("'SetItem", KSequence.EMPTY),
                new Variable("S", Sort.SET)), setKApp);
    }
}
