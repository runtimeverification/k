package org.kframework.utils;

import org.kframework.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.convertors.TstTinyOnKORE_IT;
import org.kframework.krun.KRun;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.function.BiFunction;

/**
 * Created by Manasvi on 6/19/15.
 *
 * Common Utilities shared across Tests.
 */
public class TestUtils {

    private static CompiledDefinition compiledDef;
    protected static File testResource(String baseName) throws URISyntaxException {
        return new File(TstTinyOnKORE_IT.class.getResource(baseName).toURI());
    }


    public static K getProgram(String fileName, String program, Source source) throws IOException, URISyntaxException{
        File definitionFile = testResource(fileName);
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());

        try {
            compiledDef = new Kompile(new KompileOptions(), FileUtil.testFileUtil(), kem, false).run(definitionFile, "IMP", "IMP-SYNTAX", Sorts.K());
            BiFunction<String, Source, K> programParser = compiledDef.getProgramParser(kem);
            K parsedProgram = programParser.apply(program, source);
            return parsedProgram;
        }
        finally {
            kem.print();
        }
    }

    public static Rewriter getRewriter() {

    }

}
