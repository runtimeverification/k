// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework;

import org.junit.Test;
import org.kframework.definition.Module;

import static org.junit.Assert.*;
import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

public class DefinitionTest {
    @Test
    public void testFrom() throws Exception {
        org.kframework.definition.Definition actual = Definition.from("module X endmodule");
        Module modSyntax = Module.apply("X$SYNTAX", Set());
        Module mod = new Module("X", Set(modSyntax), Set(), Att());
        assertEquals(org.kframework.definition.Definition.apply(mod, Set(mod, modSyntax), Att()), actual);
    }
}
