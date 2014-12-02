// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

public class TstKOREtoKILIT extends BaseTest {

    @Test
    public void emptyModule() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    @Test
    public void simpleSyntax() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    @Test
    public void syntaxWithAttributes() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    @Test
    public void syntaxWithRhs() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    // Ignore becuase it crashed when executed along with the other tests
    // it passes on its own
    @Test @Ignore
    public void configuration() throws IOException {
        sdfKILtoKOREtoKILTest();
    }

    @Test
    public void context() throws IOException {
        sdfKILtoKOREtoKILTest();
    }

    @Test
    public void imports() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    @Test
    public void simpleRule() throws IOException {
        sdfKILtoKOREtoKILTest();
    }

    @Test
    public void ruleWithRequiresEnsures() throws IOException {
        sdfKILtoKOREtoKILTest();
    }

    @Test
    public void syntaxPriorities() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    @Test
    public void syntaxWithPriorities() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    @Test
    public void syntaxWithOR() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    @Test
    public void userList() throws IOException {
        outerKILtoKOREtoKILTest();
    }

    @Test
    public void userListNonEmpty() throws IOException {
        outerKILtoKOREtoKILTest();
    }
}
