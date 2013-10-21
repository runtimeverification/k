package org.kframework.backend.pdmc.pda.buchi.parser;

import org.junit.Assert;
import org.junit.Test;

import org.kframework.backend.pdmc.pda.buchi.PromelaBuchi;

import java.io.ByteArrayInputStream;

/**
 * @author Traian
 */
public class PromelaBuchiParserTest {

    @Test
    public void testParse() throws Exception {
        String promelaString = "" +
                "never { /* G p -> q */\n" +
                "T0_init :    /* init */\n" +
                "\tif\n" +
                "\t:: (q) || (!p) -> goto accept_all\n" +
                "\t:: (1) -> goto T0_S2\n" +
                "\tfi;\n" +
                "T0_S2 :    /* 1 */\n" +
                "\tif\n" +
                "\t:: (1) -> goto T0_S2\n" +
                "\t:: (!p) -> goto accept_all\n" +
                "\tfi;\n" +
                "accept_all :    /* 2 */\n" +
                "\tskip\n" +
                "}\n";
        PromelaBuchi automaton = PromelaBuchiParser.parse(new ByteArrayInputStream(promelaString.getBytes("UTF-8")));
        Assert.assertTrue(automaton.initialState().isStart());

    }
}
