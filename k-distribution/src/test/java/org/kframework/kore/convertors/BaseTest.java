// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import org.apache.commons.io.FileUtils;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.kframework.attributes.Source;
import org.kframework.kil.Definition;
import org.kframework.parser.concrete2kore.CollectProductionsVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.parser.outer.Outer;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Calendar;
import java.util.function.Function;

import static org.junit.Assert.assertEquals;

public abstract class BaseTest {

    private static final String COPYRIGHT_HEADER = "// Copyright (c) " + Calendar.getInstance().get(Calendar.YEAR) + " K Team. All Rights Reserved.";
    private static final String COPYRIGHT_HEADER_REGEX = "// Copyright \\(c\\) [0-9\\-]* K Team. All Rights Reserved.";

    @Rule
    public TestName name = new TestName();

    public BaseTest() {
        super();
    }

    protected void outerOnlyTest() throws IOException {
        testConversion(this::parseUsingOuter);
    }

    public static class DefinitionWithContext {
        public final Definition definition;
        public final Context context;

        public DefinitionWithContext(Definition d, Context c) {
            this.definition = d;
            this.context = c;
            new CollectProductionsVisitor(false, c).visit(d);
        }
    }

    protected File testResource(String baseName) {
        return new File("src/test/resources" + baseName);
        // a bit of a hack to get around not having a clear working directory
        // Eclipse runs tests within k/k-distribution, IntelliJ within /k
    }

    // WARNING: only use this after checking the results manually
    private static boolean forceFixAssertionFiles = false;

    private void testConversion(Function<File, DefinitionWithContext> parse) throws IOException {
        File kilDefinitionFile = testResource("/convertor-tests/" + name.getMethodName() + ".k");
        File kilExpectedDefinitionFile = testResource("/convertor-tests/" + name.getMethodName() + expectedFilePostfix());

        DefinitionWithContext defWithContext = parse.apply(kilDefinitionFile);

        String actualOutput = convert(defWithContext);

        if (forceFixAssertionFiles) {
            PrintWriter printWriter = new PrintWriter(kilExpectedDefinitionFile);
            String sep = "\n";
            if (actualOutput.startsWith("\n"))
                sep = "";

            actualOutput = actualOutput.replaceAll(" +\n", "\n");

            printWriter.print(COPYRIGHT_HEADER + sep + actualOutput + "\n");
            printWriter.close();
        } else {
            String expectedOutput = FileUtils.readFileToString(kilExpectedDefinitionFile).replaceAll("\r\n", "\n");
            // fixing Windows line endings (git autocrlf=auto generates Windows line endings on checkout)

            assertEquals(clean(expectedOutput), clean(actualOutput));
        }
    }

    protected abstract String convert(DefinitionWithContext defWithContext);

    protected abstract String expectedFilePostfix();

    protected DefinitionWithContext parseUsingOuter(File definitionFile) {
        Definition def = new Definition();
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        def.setItems(Outer.parse(Source.apply(definitionFile.getPath()), definitionText, null));
        def.setMainModule("TEST");
        def.setMainSyntaxModule("TEST");
        Context context = new Context();
        return new DefinitionWithContext(def, context);
    }

    private String clean(String definitionText) {
        return definitionText.replaceAll(COPYRIGHT_HEADER_REGEX, "").replaceAll(" *\n", "\n").trim();
    }

}
