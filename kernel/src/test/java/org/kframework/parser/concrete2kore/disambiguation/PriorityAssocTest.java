// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.parser.concrete2kore.disambiguation;

import org.junit.Test;
import org.kframework.kore.K;
import org.kframework.parser.concrete2kore.ParserUtils;

public class PriorityAssocTest {


    @Test
    public void testConstant() throws Exception {
        String def = "module TEST syntax Exp ::= Exp \"*\" Exp [left, klabel('Mul)] > Exp \"+\" Exp [left, klabel('Plus)] | r\"[0-9]+\" [token] endmodule";
        K out1 = ParserUtils.parseWithString("1+2", "TEST", "Exp", def);
        //System.out.println("out1 = " + out1);
        K out2 = ParserUtils.parseWithString("1+2*3", "TEST", "Exp", def);
        //System.out.println("out2 = " + out2);
    }
}