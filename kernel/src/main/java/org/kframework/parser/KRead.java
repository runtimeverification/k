// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser;

import com.google.inject.Inject;

import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kast.KastFrontEnd;
import org.kframework.kast.KastOptions;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.InputModes;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.kast.KastParser;
import org.kframework.parser.kore.parser.ParseError;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Properties;

public class KRead {

    private final KExceptionManager kem;
    private final KastOptions options;
    private final KastFrontEnd.IdToKLabelsProvider idsToLabelsProvider;

    @Inject
    public KRead(
            KastOptions options,
            KExceptionManager kem,
            KastFrontEnd.IdToKLabelsProvider idsToLabelsProvider
    ) {
        this.kem = kem;
        this.options = options;
        this.idsToLabelsProvider = idsToLabelsProvider;
    }

    public K prettyRead(Module mod, Sort sort, CompiledDefinition def, Source source, String stringToParse, InputModes inputMode) {
        switch (inputMode) {
            case JSON:
                return deserialize(stringToParse, inputMode);
            case KORE:
                return parseKore(mod);
        case PROGRAM:
                return def.getParser(mod, sort, kem).apply(stringToParse, source);
            case KAST:
                return KastParser.parse(stringToParse, source);
            case BINARY:
                return BinaryParser.parse(stringToParse.getBytes());
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
        }
    }

    private K parseKore(Module mod) {
        try {
            return  KoreToK.parseKoreToK(options.fileToParse(), idsToLabelsProvider.getKoreToKLabels(), mod.sortAttributesFor());
        } catch (ParseError parseError) {
            throw KEMException.criticalError("Parse error" );
        }
    }

    public static K deserialize(String stringToParse, InputModes inputMode) {
        switch (inputMode) {
            case JSON:
                return JsonParser.parse(stringToParse);
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
        }
    }
}
