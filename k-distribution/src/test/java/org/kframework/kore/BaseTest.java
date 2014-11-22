// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;
import java.util.function.Function;

import org.apache.commons.io.FileUtils;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.parser.outer.Outer;

public abstract class BaseTest extends SDFCompilerTest {

    static final String ROOT = "src/test/resources/convertor-tests/";

    @Rule
    public TestName name = new TestName();

    public BaseTest() {
        super();
    }

    protected void outerTest() throws IOException {
        standardTest(this::parseUsingOuter);
    }

    protected void sdfTest() throws IOException {
        standardTestUsingFile(this::parseUsingSDF);
    }

    private void standardTestUsingFile(Function<File, Definition> parse) throws IOException {
        File definitionFile = new File(ROOT + name.getMethodName() + ".k").getAbsoluteFile();
        File outputFile = new File(ROOT + name.getMethodName() + "-expected.k");

        // Definition def = parseUsingOuter(definitionText);
        Definition def = parse.apply(definitionFile);

        KILtoKORE convertor = new KILtoKORE();
        org.kframework.kore.outer.Definition converted = convertor.apply(def);
        org.kframework.kore.outer.Definition koreDefintion = converted;

        String definitionText = FileUtils.readFileToString(definitionFile);

        if (outputFile.isFile()) {
            String expectedOutput = FileUtils.readFileToString(outputFile);
            assertEquals(clean(expectedOutput), clean(koreDefintion.toString()));
        } else {
            assertEquals(clean(definitionText), clean(koreDefintion.toString()));
        }
    }

    private void standardTest(Function<String, Definition> parse) throws IOException {
        File definitionFile = new File(ROOT + name.getMethodName() + ".k");
        File outputFile = new File(ROOT + name.getMethodName() + "-expected.k");

        String definitionText = FileUtils.readFileToString(definitionFile);

        // Definition def = parseUsingOuter(definitionText);
        Definition def = parse.apply(definitionText);

        KILtoKORE convertor = new KILtoKORE();
        org.kframework.kore.outer.Definition converted = convertor.apply(def);
        org.kframework.kore.outer.Definition koreDefintion = converted;

        if (outputFile.isFile()) {
            String expectedOutput = FileUtils.readFileToString(outputFile);
            assertEquals(clean(expectedOutput), clean(koreDefintion.toString()));
        } else {
            assertEquals(clean(definitionText), clean(koreDefintion.toString()));
        }
    }

    private Definition parseUsingSDF(File definitionFile) {
        try {
            return parse(definitionFile, "TEST");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private Definition parseUsingOuter(String definitionText) {
        Definition def = new Definition();
        def.setItems(Outer.parse(Sources.generatedBy(TestKILtoKORE.class), definitionText, null));
        return def;
    }

    private String clean(String definitionText) {
        return definitionText.replace("// Copyright (c) 2014 K Team. All Rights Reserved.", "")
                .trim();
    }

}