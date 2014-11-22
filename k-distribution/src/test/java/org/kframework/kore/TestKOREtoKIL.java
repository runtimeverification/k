// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import org.junit.Test;
import static org.junit.Assert.*;
import org.kframework.kil.Sources;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kore.outer.Definition;
import org.kframework.parser.outer.Outer;

public class TestKOREtoKIL {

    @Test
    public void testListConversion() {
        org.kframework.kil.Definition kilDef = new org.kframework.kil.Definition();
        String pgm = "module PGM " +
                "syntax UserLst ::= List{Elem, \",\"} " +
                "syntax NotYourUsualList ::= UserLst " +
                "syntax AnotherList ::= List{Elem2, \"!\"} " +
                "endmodule";
        kilDef.setItems(Outer.parse(Sources.generatedBy(TestKOREtoKIL.class), pgm, null));

        KILtoKORE toKore = new KILtoKORE();
        Definition koreDef = toKore.apply(kilDef);
        KOREtoKIL toKil = new KOREtoKIL();
        org.kframework.kil.Definition kilDef1 = toKil.convertDefinition(koreDef);


        final int[] lists = {0};
        BasicVisitor variableCollector = new BasicVisitor(null) {
            @Override
            public Void visit(org.kframework.kil.UserList lst, Void _void) {
                lists[0]++;
                return _void;
            }
        };
        variableCollector.visitNode(kilDef1);
        assertEquals(lists[0], 2);
    }
}
