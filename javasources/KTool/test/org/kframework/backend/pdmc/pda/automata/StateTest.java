package org.kframework.backend.pdmc.pda.automata;

import junit.framework.Assert;
import org.junit.Test;

/**
 * @author Traian
 */
public class StateTest {
    @Test
    public void testOfString() throws Exception {
        State<String, String> state = State.ofString("p");
        Assert.assertEquals("p", state.getState());
        Assert.assertNull(state.getLetter());
    }

    @Test
    public void testOfString1() throws Exception {
        State<String, String> state = State.ofString("<p,a>");
        Assert.assertEquals("p", state.getState());
        Assert.assertEquals("a", state.getLetter());
    }

    @Test
    public void testToString1() throws Exception {
        String state = State.ofString("p").toString();
        Assert.assertEquals("p", state);
    }

    @Test
    public void testToString2() throws Exception {
        String state = State.ofString("<p,a>").toString();
        Assert.assertEquals("<p,a>", state);
    }
}
