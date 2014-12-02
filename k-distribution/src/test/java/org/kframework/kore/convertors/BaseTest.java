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
import org.kframework.kil.loader.Context;
import org.kframework.parser.outer.Outer;

public abstract class BaseTest extends SDFCompilerTest {

    static final String ROOT = "src/test/resources/convertor-tests/";

    @Rule
    public TestName name = new TestName();

    public BaseTest() {
        super();
    }

    protected void outerOnlyTest() throws IOException {
        testConversion(this::parseUsingOuter);
    }

    protected void sdfTest() throws IOException {
        testConversion(this::parseUsingSDF);
    }

    static class DefintionWithContext {
        public final Definition definition;
        public final Context context;

        public DefintionWithContext(Definition d, Context c) {
            this.definition = d;
            this.context = c;
        }
    }

    private void testConversion(Function<File, DefintionWithContext> parse) throws IOException {
        File kilDefinitionFile = new File(ROOT + name.getMethodName() + ".k").getAbsoluteFile();
        File kilExpectedDefinitionFile = new File(ROOT + name.getMethodName()
                + expecteFilePostfix());

        DefintionWithContext defWithContext = parse.apply(kilDefinitionFile);

        String actualOutput = convert(defWithContext);

        if (kilExpectedDefinitionFile.isFile()) {
            String expectedOutput = FileUtils.readFileToString(kilExpectedDefinitionFile);
            assertEquals(clean(expectedOutput), clean(actualOutput));
        } else {
            String definitionText = FileUtils.readFileToString(kilDefinitionFile);
            assertEquals(clean(definitionText), clean(actualOutput));
        }
    }

    protected abstract String convert(DefintionWithContext defWithContext);

    protected abstract String expecteFilePostfix();

    private DefintionWithContext parseUsingSDF(File definitionFile) {
        try {
            return parse(definitionFile, "TEST");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private DefintionWithContext parseUsingOuter(File definitionFile) {
        Definition def = new Definition();
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        def.setItems(Outer.parse(Sources.generatedBy(TstKILtoKOREIT.class), definitionText, null));
        return new DefintionWithContext(def, null);
    }

    private String clean(String definitionText) {
        return definitionText.replace("// Copyright (c) 2014 K Team. All Rights Reserved.", "")
                .replaceAll(" *\n", "\n").trim();
    }

}
