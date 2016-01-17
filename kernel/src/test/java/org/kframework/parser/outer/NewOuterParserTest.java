// Copyright (c) 2015-2016 K Team. All Rights Reserved.

package org.kframework.parser.outer;

import com.beust.jcommander.internal.Lists;
import org.apache.commons.io.FileUtils;
import org.junit.Test;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.definition.Definition;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import java.io.File;
import java.io.IOException;

import static org.kframework.kore.KORE.*;

/**
 * Tests the K definition of the outer K syntax.
 */
public class NewOuterParserTest {
    public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();

    @Test
    public void testKOREOuter() throws IOException {
        String theTextToParse = "module FOO syntax Exp ::= Exp [stag(as(d)f)] rule ab cd [rtag(.::KList)] endmodule";
        String mainModuleName = "E-KORE";
        String mainProgramsModule = "E-KORE";
        Sort startSymbol = Sort("KDefinition");
        File definitionFile = new File(BUILTIN_DIRECTORY.toString() + "/e-kore.k");
        String definitionString = FileUtils.readFileToString(definitionFile);
        Source source = Source.apply(definitionFile.getPath());

        ParserUtils parser = new ParserUtils(FileUtil.testFileUtil()::resolveWorkingDirectory, new KExceptionManager(new GlobalOptions()));
        Definition definition = parser.loadDefinition(
                mainModuleName,
                mainProgramsModule, definitionString, definitionFile,
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY),
                false);

        K kBody = ParserUtils.parseWithModule(theTextToParse, startSymbol, source, definition.getModule(definition.att().<String>get(Att.syntaxModule()).get()).get());
        //System.out.println(kBody);
    }
}
