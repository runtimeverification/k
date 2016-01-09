// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.junit.Ignore;
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

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;

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
    public void testConcatenate() throws Exception {
        File tmp = File.createTempFile("tmp", null);
        BinaryLoader loader = new BinaryLoader(new KExceptionManager(new GlobalOptions()));
        loader.saveOrDie(tmp, term);
        K result = loader.loadOrDie(K.class, tmp);
        assertEquals(term, result);
        byte[] str = ToBinary.apply(term);
        byte[] krewrite = new byte[str.length * 2 - 8];
        System.arraycopy(str, 0, krewrite, 0, str.length - 1);
        System.arraycopy(str, 8, krewrite, str.length - 1, str.length - 9);
        krewrite[krewrite.length - 2] = BinaryParser.KREWRITE;
        krewrite[krewrite.length - 1] = BinaryParser.END;
        K result2 = BinaryParser.parse(krewrite);
        assertEquals(KRewrite(term, term), result2);
    }

    @Test @Ignore
    public void testLarger() throws Exception {
        BinaryLoader loader = new BinaryLoader(new KExceptionManager(new GlobalOptions()));
        String kast = FileUtil.testFileUtil().loadFromWorkingDirectory("/home/dwightguth/c-semantics/tmp-kcc-IxHhCoP");
        K orig = KoreParser.parse(kast, Source.apply("generated"));
        byte[] binary = ToBinary.apply(orig);
        K result = BinaryParser.parse(binary);
        assertEquals(orig, result);
    }
}
