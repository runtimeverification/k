// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.when;

import java.util.Collections;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.MapUpdate;
import org.kframework.kil.Production;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import com.google.common.collect.ImmutableList;

@RunWith(MockitoJUnitRunner.class)
public class CompileDataStructuresTest {

    @Mock
    private Context context;

    @Mock
    private Production production1;
    @Mock
    private Production production2;

    private CompileDataStructures compileDataStructures;
    private DataStructureSort mapSort;


    @Before
    public void setUp() {
        compileDataStructures = new CompileDataStructures(context);
        mapSort = new DataStructureSort("Map", "Map", "'_Map_", "'_|->_", "'.Map", Collections.singletonMap("update", "'_[_<-_]"));
    }

    /**
     * See <a href="https://github.com/kframework/k/issues/738">#738</a>
     */
    @Test
    public void testIssue738() {
        when(context.productionsOf("'_[_<-_]")).thenReturn(
                ImmutableList.of(production1));
        when(context.productionsOf("'.Map")).thenReturn(
                ImmutableList.of(production2));
        when(production1.getSort()).thenReturn("Map");
        when(production2.getSort()).thenReturn("Map");
        when(context.dataStructureSortOf("Map")).thenReturn(mapSort);
        KApp node = KApp.of(KLabelConstant.of("'_[_<-_]"), new Variable("M",
                "Map"), new Variable("F", "CId"), KApp.of("'map",
                KApp.of("'.Map")));
        ASTNode result = compileDataStructures.visit(node, null);
        assertTrue(((KList) ((KApp) ((MapUpdate) result).updateEntries()
                .values().iterator().next()).getChild()).getContents().get(0) instanceof MapBuiltin);
    }

}
