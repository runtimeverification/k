// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.io.IOException;

import org.junit.Test;
import org.kframework.kore.outer.Module;

public class TestParserOnKORE extends BaseTest {

    protected String convert(DefinitionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        org.kframework.kore.outer.Definition koreDef = kilToKore.apply(defWithContext.definition);

        BubbleParsing bubbleParsing = new BubbleParsing();
        Module koreModule = bubbleParsing.parseBubbles(koreDef.getModule("TEST").get());

        return koreModule.toString();
    }

    @Override
    protected String expectedFilePostfix() {
        return "-expected.k";
    }

    @Test public void simpleRuleKORE() throws IOException {
        outerOnlyTest();
    }

}
