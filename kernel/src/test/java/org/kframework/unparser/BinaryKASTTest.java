// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.junit.Ignore;
import org.junit.Test;
import org.kframework.kore.K;
import org.kframework.kore.mini.InjectedKLabel;
import org.kframework.kore.mini.KApply;
import org.kframework.kore.mini.KRewrite;
import org.kframework.kore.mini.KSequence;
import org.kframework.kore.mini.KToken;
import org.kframework.kore.mini.KVariable;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.utils.file.FileUtil;

import java.io.File;

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;

public class BinaryKASTTest {

    K sharedTerm = KApply.of(KLabel("_|->_"), new KToken("x", Sort("Id")), new KToken("1", Sort("Int")));
    K sharedTerm2 = new KToken("foo", Sort("Bar"));

    K term = KApply.of(KLabel("<T>"), KApply.of(KLabel("<k>"), new KSequence(sharedTerm2,
                    new KRewrite(new KVariable("Baz"), new KVariable("Baz2")), new InjectedKLabel(KLabel("_+_")), KApply.of(KLabel("foo")))),
            KApply.of(new KVariable("Lbl"), sharedTerm, sharedTerm, sharedTerm2, sharedTerm));

    @Test
    public void testWriteThenRead() throws Exception {
        byte[] str = ToBinary.apply(term);
        K result2 = BinaryParser.parse(str);
        assertEquals(term, result2);
    }

    @Test
    public void testConcatenate() throws Exception {
        byte[] str = ToBinary.apply(term);
        byte[] krewrite = new byte[str.length * 2 - 8];
        System.arraycopy(str, 0, krewrite, 0, str.length - 1);
        System.arraycopy(str, 8, krewrite, str.length - 1, str.length - 9);
        krewrite[krewrite.length - 2] = BinaryParser.KREWRITE;
        krewrite[krewrite.length - 1] = BinaryParser.END;
        K result2 = BinaryParser.parse(krewrite);
        assertEquals(new KRewrite(term, term), result2);
    }

    @Test @Ignore
    public void testLarger() throws Exception {
        byte[] kast = FileUtil.testFileUtil().loadBytes(new File("/home/dwightguth/c-semantics/tmp-kcc-FzjROvt"));
        K result = BinaryParser.parse(kast);
        System.out.println(ToKast.apply(result));
    }
}
