// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.parser.outer;

import com.beust.jcommander.internal.Lists;
import org.apache.commons.io.FileUtils;
import org.junit.Test;
import org.kframework.attributes.Source;
import org.kframework.definition.Definition;
import org.kframework.kore.K;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import java.io.File;

/**
 * Tests the K definition of the outer K syntax.
 */
public class NewOuterParserTest {
    public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();

    @Test
    public void testKOREOuter() throws Exception {
        String theTextToParse = "module FOO syntax Exp ::= Exp [stag(as(d)f)] rule ab cd [rtag(.::KList)] endmodule";
        String mainModuleName = "E-KORE";
        String mainProgramsModule = "E-KORE";
        String startSymbol = "KDefinition";
        File definitionFile = new File(BUILTIN_DIRECTORY.toString() + "/e-kore.k");
        String definitionString = FileUtils.readFileToString(definitionFile);
        Source source = Source.apply(definitionFile.getPath());

        ParserUtils parser = new ParserUtils(FileUtil.testFileUtil());
        Definition definition = parser.loadDefinition(
                mainModuleName,
                mainProgramsModule, definitionString, source,
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY),
                true);

        K kBody = ParserUtils.parseWithModule(theTextToParse, startSymbol, source, definition.mainSyntaxModule());
        //System.out.println(kBody);
    }
}
