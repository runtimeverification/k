// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

public class TestKILtoKORE extends BaseTest {

    @Test
    public void emptyModule() throws IOException {
        outerTest();
    }

    @Test
    public void simpleSyntax() throws IOException {
        outerTest();
    }

    @Test
    public void syntaxWithAttributes() throws IOException {
        outerTest();
    }

    @Test
    public void syntaxWithRhs() throws IOException {
        outerTest();
    }

    // we'll have to eventually convert the configuration
    // to macro rules, as Grigore wrote on the wiki
    // for now, we'll do this conversion:
    // <k foo="bla"> .K </k> becomes:
    // KApply(KLabel("k"), KList(EmptyK), Attributes(KApply(KLabel("foo",
    // KToken(String, "bla"))))
    @Test @Ignore
    public void configuration() throws IOException {
        sdfTest();
    }

    @Test
    public void configurationWithNested() throws IOException {
        outerTest();
    }

    // straightforward
    // again, the contents remains as a bubble
    @Test
    public void context() throws IOException {
        outerTest();
    }

    @Test
    public void imports() throws IOException {
        outerTest();
    }

    @Test
    @Ignore
    public void simpleRule() throws IOException {
        outerTest();
    }

    // straightforward, look at the kil Rule class
    // for now, the rule contents stays as a bubble
    @Test
    public void ruleWithRequiresEnsures() throws IOException {
        outerTest();
    }

    @Test
    public void ruleWithSort() throws IOException {
        outerTest();
    }

    @Test
    public void syntaxPriorities() throws IOException {
        outerTest();
    }

    @Test
    public void syntaxWithPriorities() throws IOException {
        outerTest();
    }

    @Test
    public void syntaxWithOR() throws IOException {
        outerTest();
    }

    @Test
    public void userList() throws IOException {
        outerTest();
    }
}
