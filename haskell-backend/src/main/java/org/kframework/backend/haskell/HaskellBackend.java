// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.backend.haskell;

import com.google.inject.Inject;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.Arrays;
import java.util.Set;
import java.util.EnumSet;
import java.util.HashSet;

import static org.kframework.compile.ResolveHeatCoolAttribute.Mode.*;

public class HaskellBackend extends KoreBackend {

    @Inject
    public HaskellBackend(
            KompileOptions kompileOptions,
            FileUtil files,
            KExceptionManager kem) {
        super(kompileOptions, files, kem, EnumSet.of(HEAT_RESULT, COOL_RESULT_CONDITION), false);
    }


    @Override
    public void accept(CompiledDefinition def) {
        String kore = getKompiledString(def);
        files.saveToKompiled("definition.kore", kore);
    }

    @Override
    public Set<String> excludedModuleTags() {
        return new HashSet<>(Arrays.asList("concrete", "kast"));
    }
}
