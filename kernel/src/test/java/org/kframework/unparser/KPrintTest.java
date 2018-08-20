// Copyright (c) 2015-2018 K Team. All Rights Reserved.
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
import org.kframework.parser.json.JsonParser;
import org.kframework.unparser.KPrint;
import org.kframework.unparser.OutputModes.*;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.UnsupportedEncodingException;
import java.util.Arrays;

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;

public class KPrintTest {

    K sharedTerm = KApply.of(KLabel("_|->_"), new KToken("x", Sort("Id")), new KToken("1", Sort("Int")));
    K sharedTerm2 = new KToken("foo", Sort("Bar"));

    K term = KApply.of(KLabel("<T>"), KApply.of(KLabel("<k>"), new KSequence(sharedTerm2,
                    new KRewrite(new KVariable("Baz"), new KVariable("Baz2")), new InjectedKLabel(KLabel("_+_")), KApply.of(KLabel("foo")))),
            KApply.of(new KVariable("Lbl"), sharedTerm, sharedTerm, sharedTerm2, sharedTerm));

    OutputModes[] outputModes = new OutputModes[] { OutputModes.JSON , OutputModes.BINARY };

    private String asKast(K term) throws UnsupportedEncodingException {
        return new String(new KPrint().serialize(term, OutputModes.KAST), "UTF-8");
    }

    private K unparseThenParse(K origTerm, OutputModes outputMode) throws UnsupportedEncodingException {
        byte[] unparsed = new KPrint().serialize(origTerm, outputMode);
        switch (outputMode) {
            case JSON:
                return JsonParser.parse(unparsed);
            case BINARY:
                return BinaryParser.parse(unparsed);
            default:
                return new KToken("###", Sort("UnsupportedOutputMode"));
            // TODO: How to invoke KAST parser?
            // case KAST:
            //    return KToken("hello", "false");
        }
    }

    @Test
    public void testUnparseThenParse() throws Exception {
        for (OutputModes outputMode: outputModes) {
            assertEquals(asKast(term), asKast(unparseThenParse(term, outputMode)));
        }
    }
}
