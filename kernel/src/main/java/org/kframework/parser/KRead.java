// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser;

import com.google.inject.Inject;

import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.InputModes;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.kore.KoreParser;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

public class KRead {

    private final KExceptionManager kem;

    public KRead() {
        this(new KExceptionManager(new GlobalOptions()));
    }

    @Inject
    public KRead(KExceptionManager kem) {
        this.kem = kem;
    }

    public K prettyRead(Module mod, Sort sort, CompiledDefinition def, Source source, String stringToParse, InputModes inputMode) {
        switch (inputMode) {
            case JSON:
                return deserialize(stringToParse, inputMode);
            case PROGRAM:
                return def.getParser(mod, sort, kem).apply(stringToParse, source);
            case KAST:
                return KoreParser.parse(stringToParse, source);
            case BINARY:
                return BinaryParser.parse(stringToParse.getBytes());
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
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
