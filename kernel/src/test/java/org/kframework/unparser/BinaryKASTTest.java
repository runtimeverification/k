package org.kframework.unparser;

import org.junit.Test;
import org.kframework.kore.K;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.File;

import static org.junit.Assert.assertEquals;
import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 11/16/15.
 */
public class BinaryKASTTest {

    K term = KApply(KLabel("<T>"), KApply(KLabel("<k>"), KSequence(KToken("foo", Sort("Bar")),
                    KRewrite(KVariable("Baz"), KVariable("Baz2")), InjectedKLabel(KLabel("_+_")), KApply(KLabel("foo")))),
            KApply(KLabel("<state>"), KApply(KLabel("_|->_"), KToken("x", Sort("Id")), KToken("1", Sort("Int")))));

    @Test
    public void testWriteThenRead() throws Exception {
        File tmp = File.createTempFile("tmp", null);
        BinaryLoader loader = new BinaryLoader(new KExceptionManager(new GlobalOptions()));
        loader.saveOrDie(tmp, term);
        K result = loader.loadOrDie(K.class, tmp);
        assertEquals(term, result);
        String str = ToBinary.apply(term);
        K result2 = BinaryParser.parse(str);
        assertEquals(term, result2);
    }
}
