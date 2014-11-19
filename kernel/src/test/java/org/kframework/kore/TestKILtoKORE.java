// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;
import java.util.function.Function;

import org.apache.commons.io.FileUtils;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestName;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.parser.outer.Outer;

public class TestKILtoKORE extends SDFCompilerTest {

    private static final String ROOT = "src/test/resources/convertor-tests/";

    @Rule
    public TestName name = new TestName();

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
    @Test
    public void configuration() throws IOException {
        outerTest();
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

    private void outerTest() throws IOException {
        standardTest(this::parseUsingOuter);
    }

    private void sdfTest() throws IOException {
        standardTest(this::parseUsingSDF);
    }

    private void standardTest(Function<String, Definition> parse)
            throws IOException {
        File definitionFile = new File(ROOT + name.getMethodName() + ".k");
        File outputFile = new File(ROOT + name.getMethodName() + "-expected.k");

        String definitionText = FileUtils.readFileToString(definitionFile);

        // Definition def = parseUsingOuter(definitionText);
        Definition def = parse.apply(definitionText);

        KILtoKORE convertor = new KILtoKORE();
        org.kframework.kore.outer.Definition converted = convertor.convert(def);
        org.kframework.kore.outer.Definition koreDefintion = converted;

        if (outputFile.isFile()) {
            String expectedOutput = FileUtils.readFileToString(outputFile);
            assertEquals(clean(expectedOutput), clean(koreDefintion.toString()));
        } else {
            assertEquals(clean(definitionText), clean(koreDefintion.toString()));
        }
    }

    private Definition parseUsingSDF(String definitionText) {
        Definition def = null;
        try {
            def = parse(definitionText, "TEST");
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return def;
    }

    private Definition parseUsingOuter(String definitionText) {
        Definition def = new Definition();
        def.setItems(Outer.parse(Sources.generatedBy(TestKILtoKORE.class),
                definitionText, null));
        return def;
    }

    private String clean(String definitionText) {
        return definitionText.replace(
                "// Copyright (c) 2014 K Team. All Rights Reserved.", "")
                .trim();
    }
}
