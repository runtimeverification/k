// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.definition.Definition;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;

import java.util.function.Function;

/**
 * Created by dwightguth on 9/1/15.
 */
public interface Backend {

    void accept(CompiledDefinition def);

    Function<Definition, Definition> steps(Kompile kompile);
}
