package org.kframework.backend.pdmc.pda;

import org.junit.Assert;
import org.junit.Test;

/**
 * @author Traian
 */

public class ConfigurationTest {

    @Test
    public void testOf0() throws Exception {
        Configuration<String, String> cfg = Configuration.of("<a>");
        Assert.assertTrue(cfg.stack.empty());
        Assert.assertNull(cfg.head.getLetter());
        Assert.assertEquals("a",cfg.head.getState());
    }

    @Test
    public void testOf1() throws Exception {
        Configuration<String, String> cfg = Configuration.of("<a,b>");
        assert cfg.stack.isEmpty() : "Stack must be empty, this is just a config head";
        assert cfg.head.getState().equals("a") : "the state must be 'a'";
        assert cfg.head.getLetter().equals("b") : "the stack head must be 'b'";

    }

    @Test
    public void testOf2() throws Exception {
        Configuration<String, String> cfg = Configuration.of("<p,a b c>");
        Assert.assertEquals(2,cfg.stack.size());
        Assert.assertEquals("p", cfg.head.getState());
        Assert.assertEquals("a", cfg.head.getLetter());
        Assert.assertEquals("b", cfg.stack.get(1));
        Assert.assertEquals("c", cfg.stack.get(0));
    }
}
