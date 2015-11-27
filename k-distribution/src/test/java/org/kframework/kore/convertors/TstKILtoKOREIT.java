// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;

import java.io.IOException;

@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class TstKILtoKOREIT extends BaseTest {

    @Test
    public void emptyModule() throws IOException {
        outerOnlyTest();
    }

    @Test
    public void simpleSyntax() throws IOException {
        outerOnlyTest();
    }

    @Test
    public void syntaxWithAttributes() throws IOException {
        outerOnlyTest();
    }

    @Test
    public void syntaxWithRhs() throws IOException {
        outerOnlyTest();
    }

    @Test
    public void imports() throws IOException {
        outerOnlyTest();
    }

    @Test
    public void syntaxPriorities() throws IOException {
        outerOnlyTest();
    }

    @Test
    public void syntaxWithPriorities() throws IOException {
        outerOnlyTest();
    }

    @Test
    public void syntaxWithOR() throws IOException {
        outerOnlyTest();
    }

    protected String convert(DefinitionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        org.kframework.definition.Definition koreDef = kilToKore.apply(defWithContext.definition);
        String koreDefString = koreDef.toString();
        return koreDefString;
    }

    protected String expectedFilePostfix() {
        return "-expected.k";
    }
}
