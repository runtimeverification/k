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
                "<p, b> => <p>;\n" +
                "<p, a>");
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
        System.err.print(aPostStar.toString());
        System.err.println("\n---------------------------");
        Assert.assertEquals(expectedPostStar.length(), aPostStar.toString().length());

    }

    @Test
    public void testPostStar1() throws Exception {
        PushdownSystem pds = PushdownSystem.of("" +
                "<x0, p> => <x0>;\n" +
                "<x0, p> => <x1, p p>;\n" +
                "<x1, p> => <x1, p p>;\n" +
                "<x1, p> => <x0>;\n" +
                "<x0, p>");

        PAutomaton automaton = PAutomaton.of("" +
                "x0 p <x0,out1>;" +
                "x0;" +
                "<x0,out1>");

        PAutomaton aPostStar = PostStar.postStar(pds, automaton);

        System.err.print(aPostStar.toString());

    }
}
