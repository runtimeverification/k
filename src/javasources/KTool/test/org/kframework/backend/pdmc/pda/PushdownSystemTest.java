package org.kframework.backend.pdmc.pda;

import junit.framework.Assert;
import org.junit.Test;

/**
 * @author Traian
 */
public class PushdownSystemTest {

    @Test
    public void testOf() throws Exception {
        PushdownSystem<String,String> pds = PushdownSystem.of(""+
                "<p, a> => <q, b a>;\n" +
                "<q, b> => <r, c a>;\n" +
                "<r, c> => <p, b>;\n" +
                "<p, b> => <p>;");
        Assert.assertEquals(4, pds.deltaIndex.size());
    }
}
