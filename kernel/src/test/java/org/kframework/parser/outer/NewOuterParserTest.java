// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.parser.outer;

import org.junit.Test;
import org.kframework.kore.K;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.utils.file.JarInfo;

import java.io.File;

/**
 * Tests the K definition of the outer K syntax.
 */
public class NewOuterParserTest {
    public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();

    @Test
    public void testKOREOuter() throws Exception {
        CharSequence theTextToParse = "module FOO syntax Exp ::= Exp [stag(as(d)f)] rule ab cd [rtag(.::KList)] endmodule";
        String mainModule = "KORE";
        String startSymbol = "KDefinition";
        File definitionFile = new File(BUILTIN_DIRECTORY.toString() + "/e-kore.k");

        K kBody = ParserUtils.parseWithFile(theTextToParse, mainModule, startSymbol, definitionFile);
        //System.out.println(kBody);
    }
}
