// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.junit.Ignore;
import org.junit.Test;

import org.kframework.attributes.Source;
import org.kframework.kore.K;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.kast.KastParser;

import java.io.File;
import java.io.UnsupportedEncodingException;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;

public class KPrintTest {

    private K cell(String cellName, K cellContent) {
        return KApply(KLabel(cellName), cellContent);
    }

    OutputModes[] outputModes = new OutputModes[] { OutputModes.JSON
                                                  , OutputModes.BINARY
                                                  , OutputModes.KAST
                                                  };

    private String bytes2String(byte[] input) {
        try {
            return new String(input, "UTF-8");
        } catch (UnsupportedEncodingException e) {
            throw new AssertionError("UTF-8 encoding not supported");
        }
    }

    private String asKast(K term) {
        new KPrint();
        return bytes2String(KPrint.serialize(term, OutputModes.KAST));
    }

    private K unparseThenParse(K origTerm, OutputModes outputMode) {
        new KPrint();
        byte[] unparsed = KPrint.serialize(origTerm, outputMode);
        switch (outputMode) {
            case JSON:
                return JsonParser.parse(unparsed);
            case BINARY:
                return BinaryParser.parse(unparsed);
            case KAST:
               return KastParser.parse(bytes2String(unparsed), new Source("KPrintTest"));
            default:
                return KToken("###", Sort("UnsupportedOutputMode"));
        }
    }

    @Test
    public void testUnparseThenParse() throws Exception {

        List<K> terms = new ArrayList<>();
        terms.add(KApply(KLabel("_|->_"), KToken("x", Sort("Id")), KToken("1", Sort("Int"))));
        terms.add( KToken("foo", Sort("Bar")) );
        terms.add( KApply(KLabel("_+_"), KVariable("Baz"), KVariable("Baz2")) );
        terms.add( cell("<k>", KSequence( terms.get(1)
                                      , terms.get(2)
                                      , InjectedKLabel(KLabel("_+_"))
                                      , KApply(KLabel("foo"))
                                      )
                       )
                 );
        terms.add( KApply(KLabel("<T>"), terms.get(3), KApply(KVariable("Lbl"), terms.get(0), terms.get(0), terms.get(1), terms.get(0))) );

        for (K term: terms) {
            for (OutputModes outputMode: outputModes) {
                assertEquals(asKast(term), asKast(unparseThenParse(term, outputMode)));
            }
        }
    }
}
