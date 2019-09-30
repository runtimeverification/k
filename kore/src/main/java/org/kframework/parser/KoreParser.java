package org.kframework.parser;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.parser.kore.Pattern;
import org.kframework.parser.kore.parser.ParseError;
import org.kframework.parser.kore.parser.TextToKore;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import scala.collection.Map;
import scala.Tuple2;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Properties;

import static org.kframework.Collections.*;

public class KoreParser {
    private final TextToKore textToKore;
    private final org.kframework.parser.kore.parser.KoreToK koreToK;

    public KoreParser(Map<Sort, Att> sortAttMap) {
        textToKore = new TextToKore();
        koreToK = new org.kframework.parser.kore.parser.KoreToK(stream(sortAttMap).map(t -> Tuple2.apply(t._1().name(), t._2().getOptional("hook").orElse(""))).collect(Collections.toMap()));
    }

    public K parseString(String koreString) {
        try {
            Pattern kore = textToKore.parsePattern(koreString);
            return koreToK.apply(kore);
        } catch (ParseError parseError) {
            throw KEMException.criticalError("Parse error\n", parseError );
        }
    }

    public K parseFile(File koreFile) throws ParseError {
        Pattern kore = textToKore.parsePattern(koreFile);
        return koreToK.apply(kore);
    }
}
