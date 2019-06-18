// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser;

import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.kast.KastParser;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.ByteArrayInputStream;

import javax.json.Json;
import javax.json.JsonException;
import javax.json.JsonObject;
import javax.json.JsonReader;

public class KRead {

    private final KExceptionManager kem;
    private final FileUtil files;

    public KRead(
            KExceptionManager kem,
            FileUtil files
    ) {
        this.kem = kem;
        this.files = files;
    }

    public K prettyRead(Module mod, Sort sort, CompiledDefinition def, Source source, String stringToParse, InputModes inputMode) {
        switch (inputMode) {
            case JSON:
                return deserialize(stringToParse, inputMode);
            case KORE:
                return new KoreParser(files.resolveKoreToKLabelsFile(), mod.sortAttributesFor()).parseString(stringToParse);
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

    public static K deserialize(String stringToParse, InputModes inputMode) {
        switch (inputMode) {
            case JSON:
                return JsonParser.parse(stringToParse);
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
        }
    }

    public static K autoDeserialize(byte[] kast, Source source) {
        if (BinaryParser.isBinaryKast(kast))
            return BinaryParser.parse(kast);

        try {
            JsonReader reader = Json.createReader(new ByteArrayInputStream(kast));
            JsonObject data = reader.readObject();
            return JsonParser.parseJson(data);
        } catch ( JsonException ignored ) {}

        try {
            return KastParser.parse(new String(kast), source);
        } catch ( KEMException e ) {
            throw KEMException.criticalError("Could not read input: " + source.source());
        }
    }
}
