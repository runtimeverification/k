// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import junit.framework.Assert;
import org.junit.Test;
import org.junit.rules.TestName;
import org.kframework.kore.Kompile;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.tiny.Rewriter;
import scala.Tuple2;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.function.Function;


public class TstTinyOnKORE {


    @org.junit.Rule
    public TestName name = new TestName();


    protected File testResource(String baseName) throws URISyntaxException {
        return new File(TstTinyOnKORE.class.getResource(baseName).toURI());
    }


    @Test
    public void kore_imp_tiny() throws IOException, URISyntaxException {

        String filename = "/convertor-tests/" + name.getMethodName() + ".k";

        File definitionFile = testResource(filename);
        Tuple2<Module, Function<String, K>> rwModuleAndProgramParser = Kompile.getStuff(definitionFile, "TEST", "TEST-PROGRAMS");

        Module module = rwModuleAndProgramParser._1();
        Function<String, K> programParser = rwModuleAndProgramParser._2();
        Rewriter rewriter = Kompile.getRewriter(module);

        K program = programParser.apply(
                "<top><k> while(0<=n) { s = s + n; n = n + -1; } </k><state>n|->10 s|->0</state></top>");

        long l = System.nanoTime();
        K result = rewriter.execute(program);
        System.out.println("time = " + (System.nanoTime() - l) / 1000000);

        System.out.println("result = " + result.toString());

        Assert.assertEquals("<top>(<k>(#KSequence()),<state>(_Map_(Tuple2(n:Id,-1),Tuple2(s:Id,55))))", result.toString());
    }

}
