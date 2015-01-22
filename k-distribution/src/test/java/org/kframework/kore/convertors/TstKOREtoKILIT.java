// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;
import org.kframework.kil.Definition;
import org.kframework.kore.convertors.BaseTest.DefintionWithContext;

public class TstKOREtoKILIT extends BaseTest {

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

    // Ignore becuase it crashed when executed along with the other tests
    // it passes on its own
    @Test
    @Ignore
    public void configuration() throws IOException {
        sdfTest();
    }

    @Test
    public void context() throws IOException {
        sdfTest();
    }

    @Test
    public void imports() throws IOException {
        outerOnlyTest();
    }

    @Test
    public void simpleRule() throws IOException {
        sdfTest();
    }

    @Test
    public void ruleWithRequiresEnsures() throws IOException {
        sdfTest();
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

    @Test
    public void userList() throws IOException {
        sdfTest();
    }

    @Test
    public void userListNonEmpty() throws IOException {
        sdfTest();
    }

    @Test
    public void kapp() throws IOException {
        sdfTest();
    }

    @Test
    public void complex() throws IOException {
        sdfTest();
    }

    protected String convert(DefintionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        org.kframework.kore.outer.Definition koreDef = kilToKore.apply(defWithContext.definition);
        Definition kilDefinitionTranslatedBack = new KOREtoKIL().apply(koreDef);
        String actualOutput = kilDefinitionTranslatedBack.toString();
        return actualOutput;
    }

    protected String expectedFilePostfix() {
        return "-kilexpected.k";
    }
}
