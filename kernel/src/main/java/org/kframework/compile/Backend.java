// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;

import java.util.Set;
import java.util.function.Function;

/**
 * Created by dwightguth on 9/1/15.
 */
public interface Backend {

    void accept(CompiledDefinition def);

    Function<Definition, Definition> steps();

    Function<Module, Module> specificationSteps(Definition def);

    Set<String> excludedModuleTags();
}
