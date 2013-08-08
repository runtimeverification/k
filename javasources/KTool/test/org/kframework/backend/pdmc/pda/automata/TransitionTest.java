package org.kframework.backend.pdmc.pda.automata;

import junit.framework.Assert;
import org.junit.Test;

/**
 * @author Traian
 */
public class TransitionTest {

    @Test
    public void testOf() throws Exception {
        Transition<String,String> transition = Transition.of("p a q");
        Assert.assertEquals("p", transition.getStart().getState());
        Assert.assertNull(transition.getStart().getLetter());
        Assert.assertEquals("q", transition.getEnd().getState());
        Assert.assertNull(transition.getEnd().getLetter());
        Assert.assertEquals("a", transition.getLetter());
    }

    @Test
    public void testOf1() throws Exception {
        Transition<String,String> transition = Transition.of("p q");
        Assert.assertEquals("p", transition.getStart().getState());
        Assert.assertNull(transition.getStart().getLetter());
        Assert.assertEquals("q", transition.getEnd().getState());
        Assert.assertNull(transition.getEnd().getLetter());
        Assert.assertNull(transition.getLetter());
    }

    @Test
    public void testToString() throws Exception {
        String transition = Transition.of("p a <p,a>").toString();
        Assert.assertEquals("p a <p,a>", transition);
    }

    @Test
    public void testToString1() throws Exception {
        String transition = Transition.of("p q").toString();
        Assert.assertEquals("p q", transition);
    }
}
