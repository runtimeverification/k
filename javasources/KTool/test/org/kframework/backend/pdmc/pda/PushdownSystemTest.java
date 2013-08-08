package org.kframework.backend.pdmc.pda;

import junit.framework.Assert;
import org.junit.Test;
import org.kframework.backend.pdmc.pda.automata.Automata;

/**
 * @author Traian
 */
public class PushdownSystemTest {
    @Test
    public void testPostStar() throws Exception {
        Automata<String, String> automata = Automata.of("" +
                "p a <p,out1>;" +
                "<p,out1> a <p,out2>;" +
                "<p,out2>");
        PushdownSystem<String, String> pds = PushdownSystem.of("" +
                "<p, a> => <q, b a>;\n" +
                "<q, b> => <r, c a>;\n" +
                "<r, c> => <p, b>;\n" +
                "<p, b> => <p>;");
        Automata<String,String> aPostStar = pds.postStar(automata);
        String expectedPostStar = Automata.of("" +
                "").toString();
    }

    @Test
    public void testOf() throws Exception {
        PushdownSystem<String,String> pds = PushdownSystem.<String,String>of(""+
                "<p, a> => <q, b a>;\n" +
                "<q, b> => <r, c a>;\n" +
                "<r, c> => <p, b>;\n" +
                "<p, b> => <p>;");
        Assert.assertEquals(4, pds.deltaIndex.size());
    }
}
