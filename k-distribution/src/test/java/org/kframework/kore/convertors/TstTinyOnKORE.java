// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

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


    protected File testResource(String baseName) {
        return new File(new File("k-distribution/src/test/resources" + baseName)
                .getAbsoluteFile().toString().replace("k-distribution" + File.separator + "k-distribution", "k-distribution"));
        // a bit of a hack to get around not having a clear working directory
        // Eclipse runs tests within k/k-distribution, IntelliJ within /k
    }


    @Test
    public void kore_imp_tiny() throws IOException, URISyntaxException {
//        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
//        Module moduleWithoutK = kilToKore.apply(defWithContext.definition).getModule("TEST").get();
//
//        Module module = Module("IMP", Set(moduleWithoutK), Set(
//                Production(Sort("K"), Seq(NonTerminal(Sort("KSequence"))))
//        ), Att());

        String filename = "/convertor-tests/" + name.getMethodName() + ".k";

        File definitionFile = testResource(filename);
        Tuple2<Module, Function<String, K>> rwModuleAndProgramParser = Kompile.getStuff(definitionFile, "TEST", "TEST-PROGRAMS");

        Module module = rwModuleAndProgramParser._1();
        Function<String, K> programParser = rwModuleAndProgramParser._2();
        Rewriter rewriter = Kompile.getRewriter(module);

        K program = programParser.apply(
                "<top><k> while(0<=n) { s = s + n; n = n + -1; } </k><state>n|->10 s|->0</state></top>");


//        System.out.println("rewriter = " + rewriter);


//
//
//        K program = cons.KLabel("<top>").apply(
//                cons.KLabel("<k>").apply(
//                        cons.KLabel("while__").apply(
//                                cons.KLabel("_<=_").apply((K) cons.intToToken(0), (K) cons.stringToId("n")),
//                                cons.KLabel("__").apply(
//                                        cons.KLabel("_=_;").apply(
//                                                (K) cons.stringToId("s"),
//                                                cons.KLabel("_+_").apply(
//                                                        (K) cons.stringToId("s"),
//                                                        (K) cons.stringToId("n"))),
//                                        cons.KLabel("_=_;").apply(
//                                                (K) cons.stringToId("n"),
//                                                cons.KLabel("_+_").apply(
//                                                        (K) cons.stringToId("n"),
//                                                        (K) cons.intToToken(-1)))
//                                ))),
//                cons.KLabel("<state>").apply(
//                        cons.KLabel("_Map_").apply(
//                                cons.KLabel("_|->_").apply((K) cons.stringToId("n"), (K) cons.intToToken(10)),
//                                cons.KLabel("_|->_").apply((K) cons.stringToId("s"), (K) cons.intToToken(0)))
//                )
//        );
//
////        long l = System.nanoTime();
////        Set<K> results = rewriter.rewrite(program, Set());
////        System.out.println("time = " + (System.nanoTime() - l) / 1000000);
//
//        return stream(results).map(r -> r.toString()).collect(Collections.toList()).mkString("\n");


        long l = System.nanoTime();
        K result = rewriter.execute(program);
        System.out.println("time = " + (System.nanoTime() - l) / 1000000);

        System.out.println("result = " + result.toString());
    }

}
