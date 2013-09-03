package org.kframework.backend.pdmc.pda.pautomaton;

import junit.framework.Assert;
import org.junit.Test;

/**
 * @author Traian
 */
public class PAutomatonTest {
    @Test
    public void testOf() throws Exception {
        PAutomaton automaton = PAutomaton.of("" +
                "p a <p,dummy1>;" +
                "p b <p,dummy2>;" +
                "<p,dummy1> b p;" +
                "<p,dummy2> a p;" +
                "p;" +
                "p");
        Assert.assertEquals(4, automaton.getTransitions().size());
        Assert.assertEquals(1, automaton.getFinalStates().size());
    }

    @Test
    public void testToString() throws Exception {
        String aut = "" +
                "p a <p,dummy1>;" +
                "p b <p,dummy2>;" +
                "<p,dummy1> b p;" +
                "<p,dummy2> a p;" +
                "p;" +
                "p";
        PAutomaton auto = PAutomaton.of(aut);
        String automaton = auto.toString();
        PAutomaton auto1 = PAutomaton.of(automaton);
        Assert.assertEquals(automaton,auto1.toString());
    }
}
