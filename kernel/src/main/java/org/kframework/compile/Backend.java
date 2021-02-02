// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.kompile.CompiledDefinition;

import javax.annotation.Nullable;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * Created by dwightguth on 9/1/15.
 */
public interface Backend {

    public class Holder {
        public CompiledDefinition def;

        public Holder(CompiledDefinition def) {
            this.def = def;
        }
    };

    void accept(Holder def);

    Function<Definition, Definition> steps();

    Function<Definition, Definition> proofDefinitionNonCachedSteps(@Nullable List<String> extraConcreteRuleLabels);

    Function<Module, Module> specificationSteps(Definition def);

    Set<String> excludedModuleTags();

    default ModuleTransformer restoreDefinitionModulesTransformer(Definition kompiledDefinition) {
        return ModuleTransformer.from(mod -> kompiledDefinition.getModule(mod.name()).isDefined()
                                             ? kompiledDefinition.getModule(mod.name()).get()
                                             : mod,
                "restore definition modules to same state as in definition");
    }
}
