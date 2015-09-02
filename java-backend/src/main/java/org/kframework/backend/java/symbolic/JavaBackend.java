// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.definition.Definition;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kore.compile.Backend;

import java.util.function.Function;

/**
 * Created by dwightguth on 9/1/15.
 */
public class JavaBackend implements Backend {

    @Override
    public void accept(CompiledDefinition def) {
    }

    @Override
    public Function<Definition, Definition> steps(Kompile kompile) {
        return kompile.defaultSteps();
    }
}
