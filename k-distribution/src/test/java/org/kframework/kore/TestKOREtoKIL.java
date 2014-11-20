// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import org.junit.Test;
import org.kframework.kil.Sources;
import org.kframework.kore.outer.Definition;
import org.kframework.parser.outer.Outer;

public class TestKOREtoKIL {

    @Test
    public void testListConversion() {
        org.kframework.kil.Definition kilDef = new org.kframework.kil.Definition();
        String pgm = "module PGM syntax UserLst ::= List{Elem, \",\"} endmodule";
        kilDef.setItems(Outer.parse(Sources.generatedBy(TestKOREtoKIL.class), pgm, null));

        KILtoKORE toKore = new KILtoKORE();
        Definition koreDef = toKore.convert(kilDef);
        KOREtoKIL toKil = new KOREtoKIL();
        org.kframework.kil.Definition kilDef1 = toKil.convert(koreDef);
        return;
    }
}
