// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.io.IOException;

import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;

@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class TstKILtoKOREIT extends BaseTest {

    @Test
    public void emptyModule() throws IOException {
        outerKILtoKORETest();
    }

    @Test
    public void simpleSyntax() throws IOException {
        outerKILtoKORETest();
    }

    @Test
    public void syntaxWithAttributes() throws IOException {
        outerKILtoKORETest();
    }

    @Test
    public void syntaxWithRhs() throws IOException {
        outerKILtoKORETest();
    }

    // we'll have to eventually convert the configuration
    // to macro rules, as Grigore wrote on the wiki
    // for now, we'll do this conversion:
    // <k foo="bla"> .K </k> becomes:
    // KApply(KLabel("k"), KList(EmptyK), Attributes(KApply(KLabel("foo",
    // KToken(String, "bla"))))
    @Test
    public void configuration() throws IOException {
        sdfKILtoKORETest();
    }

    @Test
    public void context() throws IOException {
        sdfKILtoKORETest();
    }

    @Test
    public void imports() throws IOException {
        outerKILtoKORETest();
    }

    @Test
    public void simpleRule() throws IOException {
        sdfKILtoKORETest();
    }

    @Test
    public void ruleWithRequiresEnsures() throws IOException {
        sdfKILtoKORETest();
    }

    @Test
    public void syntaxPriorities() throws IOException {
        outerKILtoKORETest();
    }

    @Test
    public void syntaxWithPriorities() throws IOException {
        outerKILtoKORETest();
    }

    @Test
    public void syntaxWithOR() throws IOException {
        outerKILtoKORETest();
    }

    @Test
    public void userList() throws IOException {
        outerKILtoKORETest();
    }

    @Test
    public void userListNonEmpty() throws IOException {
        sdfKILtoKORETest();
    }
}
