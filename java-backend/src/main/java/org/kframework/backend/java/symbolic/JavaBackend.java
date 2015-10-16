// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.ModuleTransformer;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kore.compile.Backend;
import org.kframework.kore.compile.ConvertDataStructureToLookup;

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
        DefinitionTransformer convertDataStructureToLookup = DefinitionTransformer.from(
                m -> ModuleTransformer.fromSentenceTransformer(new ConvertDataStructureToLookup(m, false)::convert, "convert data structures to lookups").apply(m),
                "convert data structures to lookups");
        return d -> convertDataStructureToLookup.apply(kompile.defaultSteps().apply(d));

    }
}
