// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URISyntaxException;
import java.util.function.Function;

import org.apache.commons.io.FileUtils;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.kil.loader.Context;
import org.kframework.parser.outer.Outer;

public abstract class BaseTest extends SDFCompilerTest {

    private static final String COPYRIGHT_HEADER = "// Copyright (c) 2014-2015 K Team. All Rights Reserved.";

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

    public static class DefinitionWithContext {
        public final Definition definition;
        public final Context context;

        public DefinitionWithContext(Definition d, Context c) {
            this.definition = d;
            this.context = c;
        }
    }

    private File testResource(String baseName) {
        try {
            return new File(BaseTest.class.getResource(baseName).toURI())
                    .getAbsoluteFile();
        } catch (URISyntaxException e) {
            throw new RuntimeException(e);
        }
    }

    // WARNING: only use this after checking the results manually
    private static boolean forceFixAssertionFiles = false;

    private void testConversion(Function<File, DefinitionWithContext> parse) throws IOException {
        File kilDefinitionFile = testResource("/convertor-tests/" + name.getMethodName() + ".k");
        File kilExpectedDefinitionFile = testResource(
                "/convertor-tests/" + name.getMethodName() + expectedFilePostfix());

        DefinitionWithContext defWithContext = parse.apply(kilDefinitionFile);

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
            String expectedOutput = FileUtils.readFileToString(kilExpectedDefinitionFile).replaceAll("\r\n","\n");
            // fixing Windows line endings (git autocrlf=auto generates Windows line endings on checkout)

            assertEquals(clean(expectedOutput), clean(actualOutput));
        }
    }

    protected abstract String convert(DefinitionWithContext defWithContext);

    protected abstract String expectedFilePostfix();

    private DefinitionWithContext parseUsingSDF(File definitionFile) {
        try {
            return parse(definitionFile, "TEST", false);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    protected DefinitionWithContext parseUsingOuter(File definitionFile) {
        Definition def = new Definition();
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        def.setItems(Outer.parse(Sources.generatedBy(TstKILtoKOREIT.class), definitionText, null));
        def.setMainModule("TEST");
        def.setMainSyntaxModule("TEST");
        return new DefinitionWithContext(def, null);
    }

    private String clean(String definitionText) {
        return definitionText.replace(COPYRIGHT_HEADER, "").replaceAll(" *\n", "\n").trim();
    }

}
