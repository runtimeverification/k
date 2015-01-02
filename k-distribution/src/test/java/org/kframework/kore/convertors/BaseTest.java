// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.apache.commons.io.FileUtils;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.kil.loader.Context;
import org.kframework.parser.outer.Outer;

public abstract class BaseTest extends SDFCompilerTest {

    private static final String COPYRIGHT_HEADER = "// Copyright (c) 2014 K Team. All Rights Reserved.";

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

    // WARNING: only use this after checking the results manually
    private static boolean forceFixAssertionFiles = false;

    private void testConversion(Function<File, DefintionWithContext> parse) throws IOException {
        File kilDefinitionFile = new File(ROOT + name.getMethodName() + ".k").getAbsoluteFile();
        File kilExpectedDefinitionFile = new File(ROOT + name.getMethodName()
                + expectedFilePostfix()).getAbsoluteFile();

        DefintionWithContext defWithContext = parse.apply(kilDefinitionFile);

        String actualOutput = convert(defWithContext);

        if (forceFixAssertionFiles) {
            PrintWriter printWriter = new PrintWriter(kilExpectedDefinitionFile);
            String sep = "\n";
            if(actualOutput.startsWith("\n"))
                sep = "";

            actualOutput = actualOutput.replaceAll(" +\n", "\n");

            printWriter.print(COPYRIGHT_HEADER + sep + actualOutput + "\n");
            printWriter.close();
        } else {
            String expectedOutput = FileUtils.readFileToString(kilExpectedDefinitionFile);
            assertEquals(clean(expectedOutput), clean(actualOutput));
        }
    }

    protected abstract String convert(DefintionWithContext defWithContext);

    protected abstract String expectedFilePostfix();

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
        return definitionText.replace(COPYRIGHT_HEADER, "").replaceAll(" *\n", "\n").trim();
    }

}
