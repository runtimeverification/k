// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.kframework.Collections;
import org.kframework.definition.Module;
import org.kframework.kore.Unparse;
import org.kframework.tiny.Constructors;
import org.kframework.tiny.FreeTheory;
import org.kframework.tiny.K;
import org.kframework.tiny.KApp;
import org.kframework.tiny.Rewriter;
import org.kframework.tiny.Rule;
import org.kframework.tiny.package$;
import scala.collection.immutable.Set;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.io.IOException;


public class TstTinyOnKORE extends BaseTest {


    @Test
    public void kore_imp_tiny() throws IOException {
        sdfTest();
    }

    protected String convert(DefinitionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        Module moduleWithoutK = kilToKore.apply(defWithContext.definition).getModule("TEST").get();

        Module module = Module("IMP", Set(moduleWithoutK), Set(
                Production(Sort("K"), Seq(NonTerminal(Sort("KSequence"))))
        ), Att());

        Constructors cons = new Constructors(module);

        K program = cons.KLabel("'<top>").apply(
                cons.KLabel("'<k>").apply(
                        cons.KLabel("'while__").apply(
                                cons.KLabel("'_<=_").apply((K) cons.intToToken(0),(K) cons.stringToId("n")),
                                cons.KLabel("'__").apply(
                                        cons.KLabel("'_=_;").apply(
                                                (K) cons.stringToId("s"),
                                                cons.KLabel("'_+_").apply(
                                                        (K) cons.stringToId("s"),
                                                        (K) cons.stringToId("n"))),
                                        cons.KLabel("'_=_;").apply(
                                                (K) cons.stringToId("n"),
                                                cons.KLabel("'_+_").apply(
                                                        (K) cons.stringToId("n"),
                                                        (K) cons.intToToken(-1)))
                                ))),
                cons.KLabel("'<state>").apply(
                        cons.KLabel("'_Map_").apply(
                                cons.KLabel("'_|->_").apply((K) cons.stringToId("n"), (K) cons.intToToken(100)),
                                cons.KLabel("'_|->_").apply((K) cons.stringToId("s"), (K) cons.intToToken(0)))
                ),
                cons.KLabel("'<s>").apply()
        );

//        KApp program = cons.KApply(cons.KLabel("'<top>"),
//                cons.KApply(cons.KLabel("'<k>"),
//                        cons.KApply(cons.KLabel("'_/_"), cons.stringToId("x"), cons.stringToId("y"))),
//                        cons.KApply(cons.KLabel("'<state>"),
//                                cons.KApply(cons.KLabel("'_Map_"),
//                                        cons.KApply(cons.KLabel("'_|->_"), cons.stringToId("x"), cons.intToToken(10)),
//                                        cons.KApply(cons.KLabel("'_|->_"), cons.stringToId("y"), cons.intToToken(2)))
//                        ));


        System.out.println("module = " + module);

        Rewriter rewriter = new Rewriter(module);

//        long l = System.nanoTime();
//        Set<K> results = rewriter.rewrite(program, Set());
//        System.out.println("time = " + (System.nanoTime() - l) / 1000000);
//
//        return stream(results).map(r -> r.toString()).collect(Collections.toList()).mkString("\n");

        long l = System.nanoTime();
        K result = rewriter.execute(program);
        System.out.println("time = " + (System.nanoTime() - l) / 1000000);

        return result.toString();
    }

    @Override
    protected String expectedFilePostfix() {
        return "-tiny-expected.txt";
    }
}
