// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.parser;
import com.davekoelle.AlphanumComparator;
import com.google.inject.Inject;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.InputModes;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.parser.json.JsonParser;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TTYInfo;
import scala.Tuple2;

import java.io.IOException;
import java.io.OutputStream;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import scala.Option;

import static org.kframework.kore.KORE.*;

public class KRead {

    private final KExceptionManager kem;

    public KRead() {
        this(new KExceptionManager(new GlobalOptions()));
    }

    @Inject
    public KRead(KExceptionManager kem) {
        this.kem            = kem;
    }

    public K prettyRead(Module mod, Sort sort, CompiledDefinition def, Source source, String stringToParse, InputModes inputMode) {
        switch (inputMode) {
            case KAST:
            case JSON:
                return deserialize(stringToParse, inputMode);
            case PROGRAM:
                return def.getParser(mod, sort, kem).apply(stringToParse, source);
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
        }
    }

    public static K deserialize(String stringToParse, InputModes inputMode) {
        K parsed;
        switch (inputMode) {
            case JSON:
                return JsonParser.parse(stringToParse);
            case KAST:
            default:
                throw KEMException.criticalError("Unsupported input mode: " + inputMode);
        }
    }
}
