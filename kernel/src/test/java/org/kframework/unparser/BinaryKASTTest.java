// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.junit.Test;
import org.kframework.attributes.Source;
import org.kframework.kore.K;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.kore.KoreParser;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;

import static org.junit.Assert.assertEquals;
import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 11/16/15.
 */
public class BinaryKASTTest {

    K term = KApply(KLabel("<T>"), KApply(KLabel("<k>"), KSequence(KToken("foo", Sort("Bar")),
                    KRewrite(KVariable("Baz"), KVariable("Baz2")), InjectedKLabel(KLabel("_+_")), KApply(KLabel("foo")))),
            KApply(KVariable("Lbl"), KApply(KLabel("_|->_"), KToken("x", Sort("Id")), KToken("1", Sort("Int")))));

    @Test
    public void testWriteThenRead() throws Exception {
        File tmp = File.createTempFile("tmp", null);
        BinaryLoader loader = new BinaryLoader(new KExceptionManager(new GlobalOptions()));
        loader.saveOrDie(tmp, term);
        K result = loader.loadOrDie(K.class, tmp);
        assertEquals(term, result);
        byte[] str = ToBinary.apply(term);
        K result2 = BinaryParser.parse(str);
        assertEquals(term, result2);
    }

    @Test
    public void testLarger() throws Exception {
        BinaryLoader loader = new BinaryLoader(new KExceptionManager(new GlobalOptions()));
        String kast = FileUtil.testFileUtil().loadFromWorkingDirectory("/home/dwightguth/c-semantics/tmp-kcc-IxHhCoP");
        K orig = KoreParser.parse(kast, Source.apply("generated"));
        byte[] binary = ToBinary.apply(orig);
        K result = BinaryParser.parse(binary);
        assertEquals(orig, result);
    }
}
