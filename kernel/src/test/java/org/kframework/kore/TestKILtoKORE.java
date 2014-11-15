// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;

import org.apache.commons.io.FileUtils;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestName;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.parser.outer.Outer;

public class TestKILtoKORE {

    private static final String ROOT = "src/test/resources/convertor-tests/";

    @Rule
    public TestName name = new TestName();

    @Test
    public void emptyModule() throws IOException {
        standardTest();
    }

    @Test
    public void simpleSyntax() throws IOException {
        standardTest();
    }

    @Test
    public void syntaxWithAttributes() throws IOException {
        standardTest();
    }

    @Test
    public void syntaxWithRhs() throws IOException {
        standardTest();
    }

    @Test
    @Ignore
    public void configuration() throws IOException {
        standardTest();
    }

    @Test
    @Ignore
    public void configurationWithNested() throws IOException {
        standardTest();
    }

    @Test
    @Ignore
    public void context() throws IOException {
        standardTest();
    }

    @Test
    public void imports() throws IOException {
        standardTest();
    }

    @Test
    @Ignore
    public void ruleWithRequiresEnsures() throws IOException {
        standardTest();
    }

    @Test
    @Ignore
    public void ruleWithSort() throws IOException {
        standardTest();
    }

    @Test
    public void syntaxPriorities() throws IOException {
        standardTest();
    }

    @Test
    public void syntaxWithPriorities() throws IOException {
        standardTest();
    }

    @Test
    public void syntaxWithOR() throws IOException {
        standardTest();
    }

    @Test
    public void userList() throws IOException {
        standardTest();
    }

    private void standardTest() throws IOException {
        File inputFile = new File(ROOT + name.getMethodName() + ".k");
        File outputFile = new File(ROOT + name.getMethodName() + "-expected.k");

        String definitionText = FileUtils.readFileToString(inputFile);
        org.kframework.kore.outer.Definition koreDefintion = toKORE(definitionText);

        if (outputFile.isFile()) {
            String expectedOutput = FileUtils.readFileToString(outputFile);
            assertEquals(clean(expectedOutput), clean(koreDefintion.toString()));
        } else {
            assertEquals(clean(definitionText), clean(koreDefintion.toString()));
        }
    }

    private String clean(String definitionText) {
        return definitionText.replace(
                "// Copyright (c) 2014 K Team. All Rights Reserved.", "")
                .trim();
    }

    private org.kframework.kore.outer.Definition toKORE(String testedDefintion) {
        Definition def = new Definition();
        def.setItems(Outer.parse(Sources.generatedBy(TestKILtoKORE.class),
                testedDefintion, null));

        KILtoKORE convertor = new KILtoKORE();
        org.kframework.kore.outer.Definition converted = convertor.convert(def);
        return converted;
    }
}
