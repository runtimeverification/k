package org.kframework.parser;

import org.kframework.attributes.Att;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.parser.kore.Pattern;
import org.kframework.parser.kore.parser.ParseError;
import org.kframework.parser.kore.parser.TextToKore;
import org.kframework.utils.StringUtil;
import scala.collection.Map;

import java.io.File;
import java.util.Properties;

public class KoreToK {
    public static K parseKoreToK(File koreFile, Properties idsToLabels, Map<Sort, Att> sortAttMap) throws ParseError {
        TextToKore textToKore = new TextToKore();
        Pattern kore = textToKore.parsePattern(koreFile);
        org.kframework.parser.kore.parser.KoreToK koreToK = new org.kframework.parser.kore.parser.KoreToK(idsToLabels, sortAttMap, StringUtil::enquoteKString);
        return koreToK.apply(kore);
    }
}
