// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.parser.outer;


import org.junit.Ignore;
import org.junit.Test;
import org.kframework.kore.K;
import org.kframework.parser.concrete2kore.ParserUtils;

import java.io.File;
import java.net.URISyntaxException;

public class EKoreToKoreTest {

    @Test
    @Ignore
    public void test() throws URISyntaxException {
        String theTextToParse = "module FOO syntax Exp ::= Exp [stag(as(d)f)] rule ab cd [rtag(.::KList)] endmodule";
        String mainModule = "KORE";
        String startSymbol = "KDefinition";
        File definitionFile = new File(this.getClass().getResource("/e-kore.k").toURI()).getAbsoluteFile();

        K kBody = ParserUtils.parseWithFile(theTextToParse, mainModule, startSymbol, definitionFile);

        doTransformation(kBody);
    }

    private K doTransformation(K ekore) {
        return null;
    }
}
