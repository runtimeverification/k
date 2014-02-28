package org.kframework.backend.pdmc.pda.pautomaton;

import junit.framework.Assert;
import org.junit.Test;
import org.kframework.backend.pdmc.automaton.Transition;

import java.util.Collection;

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


    @Test
    public void testGetPath() throws Exception {
        String aut =
                "p b r;\n" +
                "q a r;\n" +
                "r b p;\n" +
                "r a q;\n" +
                "q a t;\n" +
                "p;\n" +
                "t;\n";
        PAutomaton auto = PAutomaton.of(aut);
        PAutomatonState p = PAutomatonState.ofString("p");
        PAutomatonState t = PAutomatonState.ofString("t");
        Collection<Transition> path = auto.getPath(p, t);
        System.err.println("One shortest path from p to t is: " + path);
        org.junit.Assert.assertEquals("Path from p to t should have size 3", 3, path.size());
    }
}
