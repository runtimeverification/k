package org.kframework.backend.pdmc.pda.automata;

import junit.framework.Assert;
import org.junit.Test;

/**
 * @author Traian
 */
public class AutomataTest {
    @Test
    public void testOf() throws Exception {
        Automata<String,String> automata = Automata.of("" +
                "p a <p,dummy1>;" +
                "p b <p,dummy2>;" +
                "<p,dummy1> b p;" +
                "<p,dummy2> a p;" +
                "p");
        Assert.assertEquals(4, automata.getTransitions().size());
        Assert.assertEquals(1, automata.getFinalStates().size());
    }

    @Test
    public void testToString() throws Exception {
        String aut = "" +
                "p a <p,dummy1>;" +
                "p b <p,dummy2>;" +
                "<p,dummy1> b p;" +
                "<p,dummy2> a p;" +
                "p";
        Automata<String, String> auto = Automata.of(aut);
        String automata = auto.toString();
        Automata<String, String> auto1 = Automata.of(automata);
        Assert.assertEquals(automata,auto1.toString());
    }
}
