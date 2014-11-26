// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

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
        standardTest(this::parseUsingSDF);
    }

    private void standardTest(Function<File, Definition> parse) throws IOException {
        File definitionFile = new File(ROOT + name.getMethodName() + ".k").getAbsoluteFile();
        File outputFile = new File(ROOT + name.getMethodName() + "-expected.k");

        Definition def = parse.apply(definitionFile);

        KILtoKORE convertor = new KILtoKORE();
        org.kframework.kore.outer.Definition converted = convertor.apply(def);
        org.kframework.kore.outer.Definition koreDefinition = converted;

        if (outputFile.isFile()) {
            String expectedOutput = FileUtils.readFileToString(outputFile);
            assertEquals(clean(expectedOutput), clean(koreDefinition.toString()));
        } else {
            String definitionText = FileUtils.readFileToString(definitionFile);
            assertEquals(clean(definitionText), clean(koreDefinition.toString()));
        }
    }

    private Definition parseUsingSDF(File definitionFile) {
        try {
            return parse(definitionFile, "TEST");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private Definition parseUsingOuter(File definitionFile) {
        Definition def = new Definition();
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        def.setItems(Outer.parse(Sources.generatedBy(TestKILtoKOREIT.class), definitionText, null));
        return def;
    }

    private String clean(String definitionText) {
        return definitionText.replace("// Copyright (c) 2014 K Team. All Rights Reserved.", "")
                .trim();
    }

}
