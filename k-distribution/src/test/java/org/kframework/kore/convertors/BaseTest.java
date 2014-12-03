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

    protected void outerKILtoKORETest() throws IOException {
        testKILtoKORE(this::parseUsingOuter);
    }

    protected void sdfKILtoKORETest() throws IOException {
        testKILtoKORE(this::parseUsingSDF);
    }

    private void testKILtoKORE(Function<File, Definition> parse) throws IOException {
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

    protected void outerKILtoKOREtoKILTest() throws IOException {
        testKILtoKOREtoKIL(this::parseUsingOuter);
    }

    protected void sdfKILtoKOREtoKILTest() throws IOException {
        testKILtoKOREtoKIL(this::parseUsingSDF);
    }

    private void testKILtoKOREtoKIL(Function<File, Definition> parse) throws IOException {
        File kilDefinitionFile = new File(ROOT + name.getMethodName() + ".k").getAbsoluteFile();
        File kilExpectedDefinitionFile = new File(ROOT + name.getMethodName() + "-kilexpected.k");

        Definition kilDefinition = parse.apply(kilDefinitionFile);

        KILtoKORE kilToKore = new KILtoKORE();
        org.kframework.kore.outer.Definition koreDef = kilToKore.apply(kilDefinition);
        Definition kilDefinitionTranslatedBack = new KOREtoKIL().convertDefinition(koreDef);

        if (kilExpectedDefinitionFile.isFile()) {
            String expectedOutput = FileUtils.readFileToString(kilExpectedDefinitionFile);
            assertEquals(clean(expectedOutput), clean(kilDefinitionTranslatedBack.toString()));
        } else {
            String definitionText = FileUtils.readFileToString(kilDefinitionFile);
            assertEquals(clean(definitionText), clean(kilDefinitionTranslatedBack.toString()));
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
        def.setItems(Outer.parse(Sources.generatedBy(TstKILtoKOREIT.class), definitionText, null));
        return def;
    }

    private String clean(String definitionText) {
        return definitionText.replace("// Copyright (c) 2014 K Team. All Rights Reserved.", "")
                .replaceAll(" *\n", "\n").trim();
    }

}
