// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.unparser;

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import org.kframework.attributes.Source;
import org.kframework.kore.K;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.kast.KastParser;

public class KPrintTest {

  private K cell(String cellName, K cellContent) {
    return KApply(KLabel(cellName), cellContent);
  }

  OutputModes[] outputModes = new OutputModes[] {OutputModes.JSON, OutputModes.KAST};

  private String bytes2String(byte[] input) {
    return new String(input, StandardCharsets.UTF_8);
  }

  private String asKast(K term) {
    return bytes2String(KPrint.serialize(term, OutputModes.KAST));
  }

  private K unparseThenParse(K origTerm, OutputModes outputMode) {
    byte[] unparsed = KPrint.serialize(origTerm, outputMode);
    return switch (outputMode) {
      case JSON -> JsonParser.parse(unparsed);
      case KAST -> KastParser.parse(bytes2String(unparsed), new Source("KPrintTest"));
      default -> KToken("###", Sort("UnsupportedOutputMode"));
    };
  }

  @Test
  public void testUnparseThenParse() throws Exception {

    List<K> terms = new ArrayList<>();
    terms.add(KApply(KLabel("_|->_"), KToken("x", Sort("Id")), KToken("1", Sort("Int"))));
    terms.add(KToken("foo", Sort("Bar")));
    terms.add(KApply(KLabel("_+_"), KVariable("Baz"), KVariable("Baz2")));
    terms.add(
        cell(
            "<k>",
            KSequence(
                terms.get(1), terms.get(2), InjectedKLabel(KLabel("_+_")), KApply(KLabel("foo")))));
    terms.add(
        KApply(
            KLabel("<T>"),
            terms.get(3),
            KApply(KLabel("Lbl"), terms.get(0), terms.get(0), terms.get(1), terms.get(0))));

    for (K term : terms) {
      for (OutputModes outputMode : outputModes) {
        assertEquals(asKast(term), asKast(unparseThenParse(term, outputMode)));
      }
    }
  }
}
