// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser;

import static org.kframework.Collections.*;

import java.io.File;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.kore.K;
import org.kframework.kore.SortHead;
import org.kframework.parser.kore.Pattern;
import org.kframework.parser.kore.parser.ParseError;
import org.kframework.parser.kore.parser.TextToKore;
import org.kframework.utils.errorsystem.KEMException;
import scala.Tuple2;
import scala.collection.Map;

public class KoreParser {
  private final TextToKore textToKore;
  private final org.kframework.parser.kore.parser.KoreToK koreToK;

  public KoreParser(Map<SortHead, Att> sortAttMap) {
    textToKore = new TextToKore();
    koreToK =
        new org.kframework.parser.kore.parser.KoreToK(
            stream(sortAttMap)
                .map(t -> Tuple2.apply(t._1().name(), t._2().getOptional(Att.HOOK()).orElse("")))
                .collect(Collections.toMap()));
  }

  public K parseString(String koreString) {
    try {
      Pattern kore = textToKore.parsePattern(koreString);
      return koreToK.apply(kore);
    } catch (ParseError parseError) {
      throw KEMException.criticalError("Parse error\n", parseError);
    }
  }

  public K parseFile(File koreFile) throws ParseError {
    Pattern kore = textToKore.parsePattern(koreFile, 0);
    return koreToK.apply(kore);
  }
}
