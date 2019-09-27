package org.kframework.parser;

import org.kframework.attributes.Att;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.parser.kore.Pattern;
import org.kframework.parser.kore.parser.ParseError;
import org.kframework.parser.kore.parser.TextToKore;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import scala.collection.Map;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Properties;

public class KoreParser {
    private final TextToKore textToKore;
    private final org.kframework.parser.kore.parser.KoreToK koreToK;

    public KoreParser(File koreIdsToKLabelsFile, Map<Sort, Att> sortAttMap) {
        Properties idsToLabels;
        try {
            idsToLabels = new Properties();
            if (koreIdsToKLabelsFile != null) {
                FileInputStream input = new FileInputStream(koreIdsToKLabelsFile);
                idsToLabels.load(input);
            }
        } catch (IOException e) {
            throw KEMException.criticalError("Error while loading Kore to K label map", e);
        }
        textToKore = new TextToKore();
        koreToK = new org.kframework.parser.kore.parser.KoreToK(idsToLabels, sortAttMap);
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
