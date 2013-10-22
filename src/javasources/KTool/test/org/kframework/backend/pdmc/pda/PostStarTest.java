package org.kframework.backend.pdmc.pda;

import junit.framework.Assert;
import org.junit.Test;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomaton;

/**
 * @author Traian
 */
public class PostStarTest {

    @Test
    public void testPostStar() throws Exception {

        PAutomaton automaton = PAutomaton.of("" +
                "p a <p,out1>;" +
                "<p,out1> a <p,out2>;" +
                "p;" +
                "<p,out2>");
        PushdownSystem pds = PushdownSystem.of("" +
                "<p, a> => <q, b a>;\n" +
                "<q, b> => <r, c a>;\n" +
                "<r, c> => <p, b>;\n" +
                "<p, b> => <p>;");
        PAutomaton aPostStar = PostStar.postStar(pds, automaton);
        String expectedPostStar = PAutomaton.of("p a <p,out1>;" +
                "<p,out1> a <p,out2>;" +
                "p a <q,b>;" +
                "p <r,c>;" +
                "p b <r,c>;" +
                "q b <q,b>;" +
                "<q,b> a <p,out1>;" +
                "<q,b> a <q,b>;" +
                "r c <r,c>;" +
                "<r,c> a <q,b>;" +
                "p;" +
                "<p,out2>").toString();
        Assert.assertEquals(expectedPostStar.length(), aPostStar.toString().length());

    }
}
